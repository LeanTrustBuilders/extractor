import Fixture.Basic

namespace Fixture

/-- Uses a declaration of another module. -/
theorem double_triple (n : Nat) : double n + n = triple n := by
  unfold double triple; omega

end Fixture
