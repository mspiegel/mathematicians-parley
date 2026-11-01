module

public import Parley.Library

/-! Written from tests/elaborator/algebra-and-inequalities-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.InequalitiesAtAMember

theorem inequalities_at_a_member :
    (∀ i : ℕ, 0 < i → (i : ℤ) + 1 > 1) := by
  -- 1. inequalities
  have s1 : ∀ i : ℕ, 0 < i → (i : ℤ) + 1 > 1 := by intro i h_i; parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.InequalitiesAtAMember
