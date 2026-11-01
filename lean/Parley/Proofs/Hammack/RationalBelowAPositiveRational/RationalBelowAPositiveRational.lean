module

public import Parley.Library

/-! Written from proofs/hammack/rational-below-a-positive-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalBelowAPositiveRational.RationalBelowAPositiveRational

theorem rational_below_a_positive_rational (x : ℚ) (H2 : x > 0) :
    (∃ y : ℚ, y > 0 ∧ y < x) := by
  -- 1. inequalities
  have s1 : x / 2 > 0 := by parley_side
  -- 2. inequalities
  have s2 : x / 2 < x := by parley_side
  -- 3. exhibit, from 1, 2
  have s3 : ∃ y : ℚ, y > 0 ∧ y < x := ⟨x / 2, by parley_side⟩
  parley_side

end Parley.Proofs.Hammack.RationalBelowAPositiveRational.RationalBelowAPositiveRational
