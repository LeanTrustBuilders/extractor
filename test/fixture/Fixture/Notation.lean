import Fixture.Basic

namespace Fixture

/-- A notation: its parser is a node, and what it expands to (`double`) is among its dependencies. -/
notation "𝟚" n:max => double n

/-- Stated with the notation. -/
theorem double_two : 𝟚 2 = 4 := rfl

/-- An existential: its signature must show what each binder ranges over. -/
theorem exists_double (n : Nat) : ∃ (m : Nat) (_ : m ≤ 2 * n), m = double n :=
  ⟨double n, by unfold double; omega, rfl⟩

/-- A structure that extends another: its signature row must say what it extends. -/
structure BigPos extends Pos where
  big : 10 < val

end Fixture
