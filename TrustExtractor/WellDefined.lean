import Lean
import TrustAnnotations
import WellDefined
import TrustExtractor.Util

/-!
# The well-definedness facet

`well-definedness.md` §6 in LeanTrustBuilders/design. Runs the analyzer of
[WellDefined](https://github.com/LeanTrustBuilders/well-defined) on the statements of a library:
each application of a definition with a declared domain (`@[domain]`, from the library's authors or
from a catalogue imported alongside) carries an obligation, decided from what is in scope where it
sits: `discharged`, `irrelevant`, `refuted`, `open` or `unapplied`.

**Which statements.** Not every lemma: in library lemmas a use outside the domain is often
deliberate (`add_div` needs no `c ≠ 0` because `x / 0 = 0`), and reporting them all is the flood of
findings the design avoids. By default, the declarations whose statements a reader relies on:
* the claims (`@[claim]`);
* the specification theorems (`@[specifies]`) and characterizations stated by one theorem.

Others are added by name (`--decl`, `--decls-file`: the claims a project lists elsewhere, such as
`formalization.yaml`), or all theorems of some modules (`--theorems-in`), to study the analyzer.

**The facet** `welldefined` (schema `welldefined/1`) has one row per declaration analyzed, keyed by
name: `{decl, obligations}`, each obligation as `WellDefined.Obligation.asJson` writes it, or
`{decl, error}`. A declaration need not be a node of the dataset: a catalogue's dataset holds its
own theorems, and its analysis is about the library's. `meta.json` records the dischargers that ran,
their budget and the domains declared, since the results depend on them.
-/

open Lean Meta TrustAnnotations

namespace TrustExtractor.WellDefinedFacet

structure Config where
  /-- The dataset the facet is written into. -/
  dataset : System.FilePath := "dataset"
  /-- Modules to import. Empty means the dataset's modules. -/
  modules : Array Name := #[]
  /-- Declarations to analyze, besides the annotated ones. -/
  decls : Array Name := #[]
  /-- Module prefixes whose theorems are all analyzed. -/
  theoremsIn : Array Name := #[]
  /-- Whether to analyze the claims and specification theorems. -/
  annotated : Bool := true
  /-- Dischargers tried after the analyzer's default ones: a catalogue's own, typically. -/
  dischargers : Array String := #[]
  /-- Whether to try the analyzer's default dischargers. -/
  defaultDischargers : Bool := true
  /-- Each discharger's budget, in the unit of `maxHeartbeats`. -/
  heartbeats : Nat := 10000
  /-- How many declarations to analyze at once, as threads of this process. -/
  jobs : Nat := 1
  /-- Whether to write the facet into the dataset. -/
  write : Bool := true

/-- One declaration's result: a row of the facet. -/
structure Row where
  decl : Name
  obligations : Array WellDefined.Obligation := #[]
  error : Option String := none

def Row.asJson (r : Row) : Json :=
  Json.mkObj <| [("decl", toJson r.decl.toString)] ++
    (match r.error with
     | some e => [("error", toJson e)]
     | none => [("obligations", Json.arr (r.obligations.map (·.asJson)))])

/-- The declarations to analyze, in a stable order and each once: the annotated ones, those named,
then the theorems of the modules under `theoremsIn`. -/
def targets (env : Environment) (cfg : Config) : Array Name := Id.run do
  let isTheorem (n : Name) : Bool := match env.find? n with
    | some (.thmInfo _) => true
    | _ => false
  let mut out : Array Name := #[]
  if cfg.annotated then
    out := out ++ (entriesOf env `claim).map (·.decl)
    out := out ++ (specEntries env).map (·.theoremName)
    out := out ++ ((entriesOf env `characterization).map (·.decl)).filter isTheorem
  out := out ++ cfg.decls
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if cfg.theoremsIn.any (·.isPrefixOf m) then
      out := out ++ (env.header.moduleData[i]!.constNames.filter fun n =>
        isTheorem n && !n.isInternalDetail)
  let mut seen : NameSet := {}
  let mut res := #[]
  for n in out do
    unless seen.contains n do
      seen := seen.insert n
      res := res.push n
  return res

def analyze (cfg : Config) : IO (Array Row × WellDefined.Analyzer × Environment) := do
  let t0 ← IO.monoMsNow
  let mods ← if !cfg.modules.isEmpty then pure cfg.modules else do
    let mut ms := #[]
    for line in ← IO.FS.lines (cfg.dataset / "modules.jsonl") do
      if line.isEmpty then continue
      ms := ms.push ((← IO.ofExcept ((← IO.ofExcept (Json.parse line)).getObjValAs? String "name")).toName)
    pure ms
  initSearchPath (← findSysroot)
  progress t0 s!"importing {mods.size} modules"
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
  progress t0 s!"imported {env.header.moduleNames.size} modules"
  let defaults := if cfg.defaultDischargers then ({} : WellDefined.Config).dischargers else #[]
  let wcfg : WellDefined.Config :=
    { dischargers := defaults ++ cfg.dischargers, heartbeats := cfg.heartbeats }
  let unknown := cfg.dischargers.filter fun d =>
    (Parser.runParserCategory env `tactic d).toOption.isNone
  unless unknown.isEmpty do
    IO.eprintln s!"warning: dischargers that do not parse here, left out: {unknown}"
  let a := WellDefined.Analyzer.new env wcfg
  let todo := targets env cfg
  let missing := todo.filter (!env.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"warning: {missing.size} declarations to analyze are not in the environment, \
      e.g. {missing[0]!}"
  let todo := todo.filter env.contains
  progress t0 s!"{a.domains.size} declared domains; {todo.size} declarations to analyze; \
    dischargers {", ".intercalate (a.dischargers.map (·.text)).toList}"
  let run (ns : Array Name) : IO (Array Row) := ns.mapM fun n => do
    try
      return { decl := n, obligations := ← runMetaM env (a.obligationsOf n) }
    catch e => return { decl := n, error := some (toString e) }
  let k := max 1 cfg.jobs
  let chunk := (todo.size + k - 1) / k
  let tasks ← (List.range k).toArray.mapM fun j =>
    IO.asTask (run (todo.extract (j * chunk) ((j + 1) * chunk)))
  let mut rows := #[]
  for t in tasks do
    rows := rows ++ (← IO.ofExcept t.get)
  progress t0 "analyzed"
  return (rows, a, env)

/-- Runs the analysis, prints a summary, and writes the facet into the dataset. -/
def run (cfg : Config) : IO Unit := do
  let (rows, a, _) ← analyze cfg
  let obs := rows.flatMap (·.obligations)
  let count (s : WellDefined.Status) := (obs.filter (·.status == s)).size
  IO.println s!"{rows.size} declarations analyzed, {(rows.filter (!·.obligations.isEmpty)).size} \
    with uses of a definition with a declared domain; {obs.size} obligations: \
    {count .discharged} discharged, {count .irrelevant} irrelevant, {count .refuted} refuted, \
    {count .open} open, {count .unapplied} unapplied; {(rows.filter (·.error.isSome)).size} errors"
  for r in rows do
    if let some e := r.error then IO.println s!"  error {r.decl}: {e.replace "\n" " "}"
  if cfg.write then
    let name := "welldefined"
    let file := s!"facets/{name}.jsonl"
    IO.FS.createDirAll (cfg.dataset / "facets")
    writeJsonl (cfg.dataset / file) (rows.map (·.asJson))
    let metaPath := cfg.dataset / "meta.json"
    let metaJson ← IO.ofExcept (Json.parse (← IO.FS.readFile metaPath))
    let facets := ((metaJson.getObjValAs? (Array Json) "facets").toOption.getD #[]).filter fun f =>
      (f.getObjValAs? String "name").toOption != some name
    let domains := (a.domains.toArray.map (·.2)).qsort (·.decl.toString < ·.decl.toString)
    let entry := Json.mkObj [("name", toJson name), ("file", toJson file),
      ("schema", toJson "welldefined/1"), ("count", toJson rows.size),
      ("analyzer", toJson s!"WellDefined {WellDefined.version}"),
      ("dischargers", toJson (a.dischargers.map (·.text))),
      ("heartbeats", toJson a.cfg.heartbeats),
      ("domains", Json.arr (domains.map fun d =>
        Json.mkObj [("decl", toJson d.decl.toString), ("source", toJson d.source)])),
      ("targets", Json.mkObj [("annotated", toJson cfg.annotated),
        ("decls", toJson (cfg.decls.map (·.toString))),
        ("theoremsIn", toJson (cfg.theoremsIn.map (·.toString)))]),
      ("description", toJson "Each application of a definition with a declared domain, in the \
        statements analyzed, and whether its arguments are in the domain given what is in scope \
        where it sits: discharged, irrelevant (the statement says the same whatever its value), \
        refuted (the statement is about the value outside the domain), open, or unapplied")]
    IO.FS.writeFile metaPath ((metaJson.setObjVal! "facets" (Json.arr (facets.push entry))).pretty ++ "\n")
    IO.println s!"wrote {file}"

end TrustExtractor.WellDefinedFacet
