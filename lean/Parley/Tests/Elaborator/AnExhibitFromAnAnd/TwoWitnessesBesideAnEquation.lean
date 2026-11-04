module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/an-exhibit-from-an-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitFromAnAnd.TwoWitnessesBesideAnEquation

theorem two_witnesses_beside_an_equation :
    (∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ x + 1 = y + 1 - 2) := by
  -- 1. arithmetic
  have s1 : (0 + 1 : ℤ) = 2 + 1 - 2 := by parley_arith
  -- 2. arithmetic
  have s2 : (0 : ℤ) ≠ 2 := by parley_arith
  -- 3. exhibit, from 1, 2
  have s3 : ∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ x + 1 = y + 1 - 2 := ⟨(0 : ℝ), (2 : ℝ), ⟨by parley_side, by parley_side⟩⟩
  all_goals exact s3

end Parley.Tests.Elaborator.AnExhibitFromAnAnd.TwoWitnessesBesideAnEquation
