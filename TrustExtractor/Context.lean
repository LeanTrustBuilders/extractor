import MeaningGraph
import TrustExtractor.Util

/-!
# MeaningGraph's context, built faster

`MeaningGraph.Context.of` builds the tables that `Context.declDeps` (and `TrustExtractor.depsOf`)
need. One of them, `notationExpansionDeps`, walks the value of every project definition as a tree:
a value that shares subterms heavily is walked once per path to each subterm, which is exponential
in the worst case, and the walk concatenates arrays at every node. On Tau Ceti at 8befae0, a part
spent more than 18 minutes there without finishing.

`contextOf` builds the same context, with its own version of that table:

* only definitions whose value builds a `Name` (mentions `Name.str`, `Name.mkStr1`, …) are walked:
  the table records what notations expand to, which their macros store as `Name` data, and a value
  that builds no `Name` embeds none;
* the walk visits each subterm once, in the order MeaningGraph's does, so the names
  come out in the same order of first occurrence, without the repetitions. Every consumer of the
  table deduplicates, keeping first occurrences, so the dependencies are the same: `--check-deps`
  compares the table with MeaningGraph's, and the fixture has a notation.

It also reports how long each table takes, so that the next slow table shows itself.
-/

namespace TrustExtractor

open Lean MeaningGraph

/-- The constants a `Name` value is built from, as `evalNameExpr?` recognizes them. -/
def nameBuilders : Array Name :=
  #[``Name.anonymous, ``Name.str, ``Name.mkStr1, ``Name.mkStr2, ``Name.mkStr3, ``Name.mkStr4]

/-- Whether `e` mentions a constant that builds a `Name`. -/
def buildsName (e : Expr) : Bool :=
  (e.find? fun
    | .const n _ => nameBuilders.contains n
    | _ => false).isSome

/-- Walks `e` in the order of MeaningGraph's `collectEmbeddedNames`, skipping subterms already
visited, and collects the `Name` values it meets. -/
partial def embeddedNamesGo (e : Expr) : StateM (Std.HashSet Expr × Array Name) Unit := do
  if (← get).1.contains e then return
  modify fun (seen, acc) => (seen.insert e, acc)
  if let some n := evalNameExpr? e then modify fun (seen, acc) => (seen, acc.push n)
  match e with
  | .app f a => embeddedNamesGo f; embeddedNamesGo a
  | .lam _ t b _ | .forallE _ t b _ => embeddedNamesGo t; embeddedNamesGo b
  | .letE _ t v b _ => embeddedNamesGo t; embeddedNamesGo v; embeddedNamesGo b
  | .mdata _ b | .proj _ _ b => embeddedNamesGo b
  | _ => pure ()

/-- Every `Name` value embedded in `e`, as MeaningGraph's `collectEmbeddedNames` finds them, but
visiting each subterm once: the same names in the same order of first occurrence, each once. -/
def embeddedNames (e : Expr) : Array Name :=
  ((embeddedNamesGo e).run ({}, #[])).2.2

/-- MeaningGraph's `notationExpansionDeps`: each notation parser, mapped to the constants its
expansion references. -/
def notationDepsOf (env : Environment) (projectConsts : Array (Name × Name × ConstantInfo)) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for (_, _, cinfo) in projectConsts do
    if let .defnInfo v := cinfo then
      unless buildsName v.value do continue
      let names := (embeddedNames v.value).filter (env.contains ·)
      let kinds := names.filter (isNotationKind env ·)
      unless kinds.isEmpty do
        let realDeps := names.filter (!isNotationKind env ·)
        for k in kinds do
          m := m.insert k ((m.getD k #[]) ++ realDeps)
  return m

/-- `MeaningGraph.Context.of env rootPrefix`, with the notation table computed by `notationDepsOf`,
reporting the time each table takes. -/
def contextOf (env : Environment) (rootPrefix : Name) (t0 : Nat) : IO Context := do
  let t ← IO.monoMsNow
  let constants := projectConstants env rootPrefix
  let exposed : Std.HashSet Name :=
    constants.foldl (fun acc (name, _, info) =>
      if shouldExpose env rootPrefix name info then acc.insert name else acc) {}
  -- `IO.lazyPure` keeps each table from being computed before its timer starts.
  let exposed ← IO.lazyPure fun _ => exposed
  let t1 ← IO.monoMsNow
  let notationDeps ← IO.lazyPure fun _ => notationDepsOf env constants
  let t2 ← IO.monoMsNow
  let coercionInstances ← IO.lazyPure fun _ => coercionInstancesByType env rootPrefix exposed constants
  let t3 ← IO.monoMsNow
  let visibleModules ← IO.lazyPure fun _ => visibleProjectModules env rootPrefix
  let t4 ← IO.monoMsNow
  progress t0 s!"context: constants {t1 - t}ms, notations {t2 - t1}ms ({notationDeps.size}), \
    coercions {t3 - t2}ms, visibility {t4 - t3}ms"
  return { env, rootPrefix, constants, exposed, notationDeps, coercionInstances,
           declModule := constants.foldl (fun acc (name, mod, _) => acc.insert name mod) {},
           visibleModules }

end TrustExtractor
