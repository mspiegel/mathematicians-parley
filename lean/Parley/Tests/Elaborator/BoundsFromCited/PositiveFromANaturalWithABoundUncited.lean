module

public import Parley.Library

/-! Written from tests/elaborator/bounds-from-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundsFromCited.PositiveFromANaturalWithABoundUncited

theorem positive_from_a_natural_with_a_bound_uncited (n : ℕ) (H1 : 0 < n) :
    (1 ≤ (n : ℤ) ∧ (n : ℤ) > 0) := by
  -- 1. inequalities, from H1
  have s1 : 1 ≤ (n : ℤ) := by parley_side
  -- 2. inequalities, from H1
  have s2 : (n : ℤ) > 0 := by parley_side
  -- 3. join 1, 2
  have s3 : 1 ≤ (n : ℤ) ∧ (n : ℤ) > 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.BoundsFromCited.PositiveFromANaturalWithABoundUncited
