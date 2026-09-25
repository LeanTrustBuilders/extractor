import MeaningGraph

/-!
# Dependencies of many declarations, fast

MeaningGraph's `Context.allDeclDeps` computes, for every exposed declaration, three lists — the
statement's constants, the statement and value's, and the statement and data's — sequentially, and
deduplicates each with a linear scan. On Tau Ceti that walks every proof term (the `term` notion
needs them) and is quadratic in the length of long dependency lists: a part of 10,000 declarations
took four minutes.

This module computes the same lists from MeaningGraph's public pieces (`usedConstantsOf`,
`expandThroughInternals`, the `Context` tables), with three differences:

* the value's constants, proofs included, are computed only when the `term` notion is asked for;
  the `meaning` notion never needs a theorem's proof;
* deduplication uses a hash set;
* declarations are processed in parallel chunks, each chunk threading its own expansion cache.

The results agree with `Context.declDeps` edge for edge: `test/run.sh` compares the two on the
fixture.
-/

namespace TrustExtractor

open Lean MeaningGraph

/-- The dependencies of one declaration under each notion. `term` is empty when not computed. -/
structure Deps where
  statement : Array Name
  meaning : Array Name
  term : Array Name
deriving Inhabited

/-- `cs` without duplicates, without `self`, and without dependencies on project modules that the
declaration's module does not import (MeaningGraph's import-visibility check). -/
def dedupDeps (ctx : Context) (self : Name) (cs : Array Name) : Array Name := Id.run do
  let visible := ctx.visibleModules.getD (ctx.declModule.getD self .anonymous) {}
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for c in cs do
    if c == self || seen.contains c then continue
    seen := seen.insert c
    match ctx.declModule.get? c with
    | some mod => if visible.contains mod then out := out.push c
    | none => out := out.push c
  return out

/-- MeaningGraph's addition of coercion instances whose coerced-from type the constants mention. -/
def addCoercionInsts (ctx : Context) (cs : Array Name) : Array Name :=
  let present : Std.HashSet Name := cs.foldl (fun acc c => acc.insert c) {}
  cs ++ cs.foldl (init := #[]) fun acc c =>
    acc ++ (ctx.coercionInstances.getD c #[]).filterMap fun inst =>
      if inst.witnesses.all present.contains then some inst.name else none

/-- The dependencies of one declaration. `isProp`: whether it is a proof, whose meaning is its
statement. -/
def declDeps (ctx : Context) (cache : Cache) (name : Name) (info : ConstantInfo) (isProp : Bool)
    (withTerm : Bool) : Deps × Cache := Id.run do
  let env := ctx.env
  let notationDeps := ctx.notationDeps.getD name #[]
  let expand (cache : Cache) (cs : Array Name) : Array Name × Cache :=
    expandThroughInternals env ctx.rootPrefix ctx.exposed cache (addCoercionInsts ctx cs)
  let typeUsed := usedConstantsOf env name info false
  let (statement, cache) := expand cache typeUsed
  let (meaning, cache) :=
    if isProp then (statement, cache)
    else match ctx.dataValueConsts.get? name with
      | some valueConsts => expand cache (typeUsed ++ valueConsts ++ notationDeps)
      | none => expand cache (usedConstantsOf env name info true ++ notationDeps)
  let (term, cache) :=
    if withTerm then expand cache (usedConstantsOf env name info true ++ notationDeps)
    else (#[], cache)
  return ({ statement := dedupDeps ctx name statement, meaning := dedupDeps ctx name meaning
            term := dedupDeps ctx name term }, cache)

/-- The dependencies of `targets`, computed in parallel chunks of `chunk` declarations. -/
def depsOf (ctx : Context) (targets : Array (Name × ConstantInfo × Bool)) (withTerm : Bool)
    (chunk : Nat := 256) : IO (Array (Name × Deps)) := do
  let chunks := (Array.range ((targets.size + chunk - 1) / chunk)).map fun i =>
    targets.extract (i * chunk) ((i + 1) * chunk)
  let tasks := chunks.map fun part => Task.spawn (prio := .dedicated) fun _ => Id.run do
    let mut cache : Cache := {}
    let mut out : Array (Name × Deps) := #[]
    for (name, info, isProp) in part do
      let (d, cache') := declDeps ctx cache name info isProp withTerm
      cache := cache'
      out := out.push (name, d)
    return out
  return tasks.foldl (fun acc t => acc ++ t.get) #[]

end TrustExtractor
