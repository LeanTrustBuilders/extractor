import Lean
import TrustExtractor.Util

/-!
# The `statement` facet: a declaration's statement, taken apart

What a reader needs to judge a statement without opening Lean, as Referee's "statement anatomy"
shows it: the binders of the declaration's type, each with the role it plays, and what is claimed or
defined under them.

* A binder whose type is a proposition is a **hypothesis**; one whose type is a sort (or a family of
  sorts) is a **type**; an instance-implicit binder is an **instance**, which a view shows next to
  the binder it is about; everything else is a **variable**.
* Names are printed from inside the declaration's namespace, as its source reads them.
* `conclusion` is what remains of the type under the binders: for a theorem, the claim; for a
  definition, the type of what it defines.
* For a definition that is not a proof, `value` is its body with the binders in place, pretty-printed
  with a bounded number of steps (`⋯` marks what was cut), since a body can be arbitrarily large.
* For a structure or class, `fields`; for another inductive type, `constructors`.

Everything is pretty-printed by Lean itself, with its default notation, so the text is what a Lean
user would write. The facet is computed in parallel chunks, each with its own `MetaM` run.
-/

namespace TrustExtractor

open Lean Meta

/-- Pretty-prints `e` in at most `steps` delaborator steps, on lines of 100 characters. -/
def ppBounded (e : Expr) (steps : Nat) : MetaM String := do
  let fmt ← withOptions (fun o => pp.proofs.set (pp.maxSteps.set o steps) false) (ppExpr e)
  return fmt.pretty 100

/-- A binder's name as written; empty for a name the source cannot refer to (an anonymous instance
binder's `inst✝`, an auto-bound variable), which a view shows by its type alone. -/
def binderDisplayName (n : Name) : String :=
  if n.hasMacroScopes || n.isAnonymous then "" else n.toString

/-- The role a local hypothesis plays in a statement. -/
def binderRole (decl : LocalDecl) : MetaM String := do
  if decl.binderInfo.isInstImplicit then return "instance"
  let ty ← instantiateMVars decl.type
  if (← isProp ty) then return "hypothesis"
  if ty.getForallBody.isSort then return "type"
  return "variable"

/-- The binders `xs` as JSON rows. -/
def bindersJson (xs : Array Expr) : MetaM (Array Json) :=
  xs.mapM fun x => do
    let decl ← x.fvarId!.getDecl
    return Json.mkObj [("name", toJson (binderDisplayName decl.userName)),
      ("type", toJson (← ppBounded decl.type 2000)), ("role", toJson (← binderRole decl)),
      ("explicit", toJson decl.binderInfo.isExplicit)]

/-- The fields of a structure, or the constructors of another inductive type, with its parameters
`params` in place. -/
def membersJson (name : Name) (params : Array Expr) : MetaM (String × Array Json) := do
  let env ← getEnv
  let some (.inductInfo ind) := env.find? name | return ("", #[])
  if isStructure env name then
    let some (.ctorInfo ctor) := env.find? (ind.ctors.headD .anonymous) | return ("", #[])
    let ty ← instantiateForall ctor.type params
    let fields ← forallTelescope ty fun ys _ => ys.mapM fun y => do
      let decl ← y.fvarId!.getDecl
      return Json.mkObj [("name", toJson decl.userName.eraseMacroScopes.toString),
        ("type", toJson (← ppBounded decl.type 2000))]
    return ("fields", fields)
  let ctors ← ind.ctors.toArray.mapM fun c => do
    let some info := env.find? c | return Json.null
    let ty ← instantiateForall info.type params
    return Json.mkObj [("name", toJson (c.replacePrefix name .anonymous).toString),
      ("type", toJson (← ppBounded ty 2000))]
  return ("constructors", ctors)

/-- The `statement` facet row of one declaration. -/
def statementRow (name : Name) (info : ConstantInfo) (isProp : Bool) : MetaM Json := do
  -- Printed from inside the declaration's namespace, as its source reads: `triple n` rather than
  -- `Fixture.triple n` for a statement in namespace `Fixture`.
  withTheReader Core.Context (fun c => { c with currNamespace := name.getPrefix }) do
  forallTelescope info.type fun xs body => do
    let mut fields := #[("decl", toJson name.toString), ("binders", toJson (← bindersJson xs)),
      ("conclusion", toJson (← ppBounded body 2000))]
    match info with
    | .defnInfo v =>
      unless isProp do
        let value := v.value.beta xs
        let text ← ppBounded value 300
        fields := fields.push ("value", toJson text)
    | .inductInfo ind =>
      let (key, members) ← membersJson name (xs.extract 0 ind.numParams)
      unless key.isEmpty do fields := fields.push (key, toJson members)
    | _ => pure ()
    return Json.mkObj fields.toList

/-- The `statement` facet rows of `targets`, in parallel chunks of `chunk`. A declaration whose
statement cannot be taken apart (the pretty-printer failed on it) gets no row. -/
def statementRows (env : Environment) (targets : Array (Name × ConstantInfo × Bool))
    (chunk : Nat := 200) : IO (Array Json) := do
  let chunks := (Array.range ((targets.size + chunk - 1) / chunk)).map fun i =>
    targets.extract (i * chunk) ((i + 1) * chunk)
  let tasks ← chunks.mapM fun part => IO.asTask (runMetaM env do
    part.filterMapM fun (name, info, isProp) => do
      try some <$> statementRow name info isProp catch _ => pure none)
  let mut out := #[]
  for t in tasks do
    out := out ++ (← IO.ofExcept t.get)
  return out

end TrustExtractor
