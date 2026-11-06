module

public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/algebra-and-inequalities-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.InequalitiesAtAMember

theorem inequalities_at_a_member :
    (∀ i : ℤ, 0 < i → i + 1 > 1) := by
  -- 1. inequalities
  have s1 : ∀ i : ℤ, 0 < i → i + 1 > 1 := by intro i h_i; parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.InequalitiesAtAMember
