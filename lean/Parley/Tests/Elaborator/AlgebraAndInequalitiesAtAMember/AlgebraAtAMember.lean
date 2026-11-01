module

public import Parley.Library

/-! Written from tests/elaborator/algebra-and-inequalities-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.AlgebraAtAMember

theorem algebra_at_a_member (n : ℕ) (hH1 : 0 < n) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 (n : ℤ) → i + i = 2 * i) := by
  -- 1. algebra
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 (n : ℤ) → i + i = 2 * i := by intro i h_i; parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.AlgebraAtAMember
