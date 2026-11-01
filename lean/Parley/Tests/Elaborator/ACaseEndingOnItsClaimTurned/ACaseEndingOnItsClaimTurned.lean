module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/a-case-ending-on-its-claim-turned.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACaseEndingOnItsClaimTurned.ACaseEndingOnItsClaimTurned

theorem a_case_ending_on_its_claim_turned (x : ℝ) (y : ℝ) (hH3 : x < y) :
    y ≠ x := by
  -- 1. mun:nonneg-or-neg
  have s1 : x ≥ 0 ∨ x < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x))
  -- 2. cases, from 1
  have s2 : y ≠ x := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. inequalities
      have s2_1 : x ≠ y := by parley_side
      all_goals parley_side
    · skip
      -- 2.2. inequalities
      have s2_2 : y ≠ x := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ACaseEndingOnItsClaimTurned.ACaseEndingOnItsClaimTurned
