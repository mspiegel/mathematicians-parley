module

public import Parley.Library

/-! Written from tests/elaborator/an-exhibit-from-an-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitFromAnAnd.TwoWitnessesBesideAnEquation

theorem two_witnesses_beside_an_equation :
    (∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ x + 1 = y + 1 - 2) := by
  -- 1. arithmetic
  have s1 : (0 + 1 : ℤ) = 2 + 1 - 2 := by norm_num
  -- 2. arithmetic
  have s2 : (0 : ℤ) ≠ 2 := by norm_num
  -- 3. exhibit, from 1, 2
  have s3 : ∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ x + 1 = y + 1 - 2 := ⟨(0 : ℝ), (2 : ℝ), by parley_side⟩
  parley_side

end Parley.Tests.Elaborator.AnExhibitFromAnAnd.TwoWitnessesBesideAnEquation
