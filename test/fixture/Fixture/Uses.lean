import Fixture.Basic

namespace Fixture

/-- Uses a declaration of another module. -/
@[specifies double "relates it to `triple`", specifies triple]
theorem double_triple (n : Nat) : double n + n = triple n := by
  unfold double triple; omega

/-- A predicate characterizing `double`. -/
@[characterization property double "the defining equation"]
def IsDouble (n m : Nat) : Prop := m = n + n

@[characterization existence]
theorem isDouble_double (n : Nat) : IsDouble n (double n) := by unfold IsDouble double; omega

@[characterization uniqueness]
theorem IsDouble.unique {n a b : Nat} (ha : IsDouble n a) (hb : IsDouble n b) : a = b := by
  unfold IsDouble at *; omega

-- A unit test: an `example`, which the compiled library does not keep (scripts/examples.py finds it).
example : double 2 = 4 := rfl

end Fixture
