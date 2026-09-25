import Lean
import TrustExtractor.Util

/-!
# The `statement` and `signature` facets: statements a reader can take apart and hover over

What a reader needs to judge a statement without opening Lean, as Referee's "statement anatomy"
shows it: the binders of the declaration's type, each with the role it plays, and what is claimed or
defined under them.

* A binder whose type is a proposition is a **hypothesis**; one whose type is a sort (or a family of
  sorts) is a **type**; an instance-implicit binder, or any binder whose type is a class, is an
  **instance**, which a view shows next to the binder it is about; everything else is a
  **variable**. Each binder also records the **head** constant of its type, whose docstring a view
  can quote as a gloss.
* Names are printed from inside the declaration's namespace, as its source reads them.
* `conclusion` is what remains of the type under the binders: for a theorem, the claim; for a
  definition, the type of what it defines.
* For a definition that is not a proof, `value` is its body with the binders in place, pretty-printed
  with a bounded number of steps (`⋯` marks what was cut), since a body can be arbitrarily large.
* For a structure or class, `fields`; for another inductive type, `constructors`.
* Every printed text comes with `refs`: for each identifier that stands for a constant, its span
  (`[start, stop)`, in characters) and the constant's name, read off the pretty-printer's own
  record of which subterm each piece of text came from. This is what lets a view put a hover on
  `ℕ` that says what `Nat` is. `--no-refs` leaves them out.

The `signature` facet is each node's signature as Lean prints it (`name (x : α) … : β`), for
project and upstream nodes alike: what a hover shows for a constant. Both facets are computed in
parallel chunks, each with its own `MetaM` run.
-/

namespace TrustExtractor

open Lean Meta

/-- Pretty-printing options: a bounded number of delaborator steps, proofs elided. -/
def ppOptions (steps : Nat) (o : Options) : Options :=
  pp.proofs.set (pp.maxSteps.set o steps) false

/-- Pretty-prints `e` in at most `steps` delaborator steps, on lines of 100 characters. -/
def ppBounded (e : Expr) (steps : Nat) : MetaM String := do
  let fmt ← withOptions (ppOptions steps) (ppExpr e)
  return fmt.pretty 100

/-- The constant a pretty-printer tag stands for, if it stands for one. -/
def tagConst? (infos : PrettyPrinter.InfoPerPos) (tag : Nat) : Option Name :=
  match infos.get? tag with
  | some (.ofTermInfo ti) => ti.expr.consumeMData.constName?
  -- The head of an application is recorded with the extra hover information delaboration adds.
  | some (.ofDelabTermInfo ti) => ti.expr.consumeMData.constName?
  | _ => none

/-- Lays out tagged text, recording where each constant's tag starts and stops (in characters). -/
partial def layOut (infos : PrettyPrinter.InfoPerPos) :
    Widget.TaggedText (Nat × Nat) → StateM (Array String × Nat × Array (Nat × Nat × Name)) Unit
  | .text s => modify fun (out, pos, refs) => (out.push s, pos + s.length, refs)
  | .append ts => ts.forM (layOut infos)
  | .tag (n, _) t => do
    let start := (← get).2.1
    layOut infos t
    if let some c := tagConst? infos n then
      modify fun (out, pos, refs) => (out, pos, refs.push (start, pos, c))

/-- The references worth a hover: trimmed of surrounding whitespace, none that is only punctuation,
and only the innermost. A notation's tag covers the whole notation (`A x = a` for `Eq`), and the
operator inside it (`=`) has a tag of its own; keeping the innermost puts the hover on the operator,
as an editor does, and not on everything around it. -/
def cleanRefs (text : String) (refs : Array (Nat × Nat × Name)) : Array (Nat × Nat × Name) := Id.run do
  let cs := text.toList.toArray
  let mut trimmed := #[]
  for (s0, t0, c) in refs do
    let mut s := s0
    let mut t := min t0 cs.size
    while s < t && cs[s]!.isWhitespace do s := s + 1
    while t > s && cs[t - 1]!.isWhitespace do t := t - 1
    if (cs.extract s t).any fun ch => !(ch.isWhitespace || ",;()[]{}⟨⟩".contains ch) then
      trimmed := trimmed.push (s, t, c)
  let inner := trimmed.filter fun (s, t, _) =>
    !trimmed.any fun (s', t', _) => s ≤ s' && t' ≤ t && (s', t') != (s, t)
  return (inner.toList.eraseDups.toArray).qsort (·.1 < ·.1)

/-- `e` pretty-printed, as `(text, refs)`: the text, and `[start, stop, constant]` for each identifier
in it that stands for a constant. -/
def ppWithRefs (e : Expr) (steps : Nat) : MetaM (String × Json) := do
  -- `pp.tagAppFns`: the head of an application gets a tag of its own, as the editor's infoview has
  -- it, so that `Fin` in `Fin K` can have a hover and not only the whole `Fin K`.
  let fwi ← withOptions (fun o => (ppOptions steps o).setBool `pp.tagAppFns true)
    (PrettyPrinter.ppExprWithInfos e)
  let tt := Widget.TaggedText.prettyTagged fwi.fmt (w := 100)
  let ((), (out, _, refs)) := (layOut fwi.infos tt).run (#[], 0, #[])
  let text := String.join out.toList
  let refs := cleanRefs text refs
  return (text,
    Json.arr (refs.map fun (s, t, c) => Json.arr #[toJson s, toJson t, toJson c.toString]))

/-- A text field and, when `withRefs`, its `…Refs` companion. -/
def textFields (key : String) (e : Expr) (steps : Nat) (withRefs : Bool) : MetaM (List (String × Json)) := do
  if withRefs then
    let (text, refs) ← ppWithRefs e steps
    return [(key, toJson text), (key ++ "Refs", refs)]
  return [(key, toJson (← ppBounded e steps))]

/-- A binder's name as written; empty for a name the source cannot refer to (an anonymous instance
binder's `inst✝`, an auto-bound variable), which a view shows by its type alone. -/
def binderDisplayName (n : Name) : String :=
  if n.hasMacroScopes || n.isAnonymous then "" else n.toString

/-- The role a local hypothesis plays in a statement. A binder whose type is a class application is
an instance whatever its brackets (`{mΩ : MeasurableSpace Ω}` as much as `[NeZero K]`): it is
structure put on another binder, which a view shows next to it. -/
def binderRole (decl : LocalDecl) : MetaM String := do
  if decl.binderInfo.isInstImplicit then return "instance"
  let ty ← instantiateMVars decl.type
  if (← isClass? ty).isSome then return "instance"
  if (← isProp ty) then return "hypothesis"
  if ty.getForallBody.isSort then return "type"
  return "variable"

/-- The head constant of a type, if it has one: `NeZero` for `NeZero K`, `Nat` for `ℕ`. -/
def headConst? (ty : Expr) : Option Name :=
  ty.consumeMData.getAppFn.constName?

/-- The binders `xs` as JSON rows. -/
def bindersJson (xs : Array Expr) (withRefs : Bool) : MetaM (Array Json) :=
  xs.mapM fun x => do
    let decl ← x.fvarId!.getDecl
    let head := (headConst? decl.type).map (·.toString)
    return Json.mkObj <| [("name", toJson (binderDisplayName decl.userName))] ++
      (← textFields "type" decl.type 2000 withRefs) ++
      [("role", toJson (← binderRole decl)), ("explicit", toJson decl.binderInfo.isExplicit),
       ("implicit", toJson (decl.binderInfo.isImplicit || decl.binderInfo.isStrictImplicit))] ++
      (head.map fun h => [("head", toJson h)]).getD []

/-- The fields of a structure, or the constructors of another inductive type, with its parameters
`params` in place. -/
def membersJson (name : Name) (params : Array Expr) (withRefs : Bool) : MetaM (String × Array Json) := do
  let env ← getEnv
  let some (.inductInfo ind) := env.find? name | return ("", #[])
  if isStructure env name then
    let some (.ctorInfo ctor) := env.find? (ind.ctors.headD .anonymous) | return ("", #[])
    let ty ← instantiateForall ctor.type params
    let fields ← forallTelescope ty fun ys _ => ys.mapM fun y => do
      let decl ← y.fvarId!.getDecl
      return Json.mkObj <| [("name", toJson decl.userName.eraseMacroScopes.toString)] ++
        (← textFields "type" decl.type 2000 withRefs)
    return ("fields", fields)
  let ctors ← ind.ctors.toArray.mapM fun c => do
    let some info := env.find? c | return Json.null
    let ty ← instantiateForall info.type params
    return Json.mkObj <| [("name", toJson (c.replacePrefix name .anonymous).toString)] ++
      (← textFields "type" ty 2000 withRefs)
  return ("constructors", ctors)

/-- The `statement` facet row of one declaration. -/
def statementRow (name : Name) (info : ConstantInfo) (isProp : Bool) (withRefs : Bool) : MetaM Json := do
  -- Printed from inside the declaration's namespace, as its source reads: `triple n` rather than
  -- `Fixture.triple n` for a statement in namespace `Fixture`.
  withTheReader Core.Context (fun c => { c with currNamespace := name.getPrefix }) do
  forallTelescope info.type fun xs body => do
    let mut fields : List (String × Json) := [("decl", toJson name.toString),
      ("binders", toJson (← bindersJson xs withRefs))]
    fields := fields ++ (← textFields "conclusion" body 2000 withRefs)
    if let some h := headConst? body then fields := fields ++ [("conclusionHead", toJson h.toString)]
    match info with
    | .defnInfo v =>
      unless isProp do
        fields := fields ++ (← textFields "value" (v.value.beta xs) 300 withRefs)
    | .inductInfo ind =>
      let (key, members) ← membersJson name (xs.extract 0 ind.numParams) withRefs
      unless key.isEmpty do fields := fields ++ [(key, toJson members)]
    | _ => pure ()
    return Json.mkObj fields

/-- Runs `f` on `targets` in parallel chunks of `chunk`, each in its own `MetaM` run, keeping the
rows it produces. A row whose computation throws (the pretty-printer failed on it) is dropped. -/
def rowsInParallel {α : Type} (env : Environment) (targets : Array α) (f : α → MetaM Json)
    (chunk : Nat := 200) : IO (Array Json) := do
  let chunks := (Array.range ((targets.size + chunk - 1) / chunk)).map fun i =>
    targets.extract (i * chunk) ((i + 1) * chunk)
  let tasks ← chunks.mapM fun part => IO.asTask (runMetaM env do
    part.filterMapM fun t => do try some <$> f t catch _ => pure none)
  let mut out := #[]
  for t in tasks do
    out := out ++ (← IO.ofExcept t.get)
  return out

/-- The `statement` facet rows of `targets`. -/
def statementRows (env : Environment) (targets : Array (Name × ConstantInfo × Bool)) (withRefs : Bool) :
    IO (Array Json) :=
  rowsInParallel env targets fun (name, info, isProp) => statementRow name info isProp withRefs

/-- The `signature` facet rows of `names`: each constant's signature as Lean prints it. -/
def signatureRows (env : Environment) (names : Array Name) : IO (Array Json) :=
  rowsInParallel env names fun name => do
    let fwi ← withOptions (ppOptions 400) (PrettyPrinter.ppSignature name)
    return Json.mkObj [("decl", toJson name.toString), ("text", toJson (fwi.fmt.pretty 100))]

end TrustExtractor
