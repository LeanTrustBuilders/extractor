import SemanticHash
import TrustExtractor.Util

/-!
# The three hashes of a declaration key

* **meaning**: semantic_hash's proof-irrelevant hash. Deep: a referenced constant contributes its own
  hash, so it changes when anything the declaration's statement or data rests on changes meaning.
* **content**: semantic_hash's proof-relevant hash. Deep, and it also changes when a proof changes.
* **local** (`ltb-local-v1`, defined here): the declaration's own statement and data, hashed with
  semantic_hash's expression hasher, with every referenced constant contributing a hash of its
  *name* instead of its content. It changes when the declaration itself is rewritten, and not when
  something it uses changes underneath. Invariant under renaming of binders and universe parameters,
  like the other two.

A review records all three. The meaning hash decides whether the review is current; when it is not,
the local hash tells "the declaration changed" from "something underneath changed".
-/

namespace TrustExtractor

open Lean

/-- The name of the local hash function, recorded in `meta.json`. Bump it whenever `localHash`
changes, since stored reviews compare against it. -/
def localHasherName : String := "ltb-local-v1"

/-- The local hash of a declaration: its own statement and data, references by name.

* theorems, axioms, opaque constants: the statement only (a proof is not part of what is reviewed,
  and an opaque body is hidden by design);
* definitions: the statement and the value;
* inductive types and structures: the type, the number of parameters, and each constructor's type.
-/
def localHash (env : Environment) (info : ConstantInfo) : BaseIO UInt64 := do
  let h (e : Expr) : BaseIO UInt64 := SemanticHash.Hashing.hashExpr {} e
  let ty ← h info.type
  match info with
  | .defnInfo v => return mixHash 2 (mixHash ty (← h v.value))
  | .inductInfo v =>
    let mut acc := mixHash 3 (mixHash ty (hash v.numParams))
    for c in v.ctors do
      if let some ci := env.find? c then
        acc := mixHash acc (← h ci.type)
    return acc
  | .thmInfo _ => return mixHash 1 ty
  | _ => return mixHash 4 ty

end TrustExtractor
