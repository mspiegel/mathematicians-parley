module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/a-case-ending-on-its-claim-turned.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACaseEndingOnItsClaimTurned.ACaseEndingOnItsClaimTurned

theorem a_case_ending_on_its_claim_turned (x : ℝ) (y : ℝ) (H3 : x < y) :
    y ≠ x := by
  -- 1. mun:nonneg-or-neg
  have s1 : x ≥ 0 ∨ x < 0 := by simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x))
  -- 2. cases, from 1
  have s2 : y ≠ x := by
    rcases s1 with C1 | C2
    · skip
      -- 2.1. inequalities
      have s2_1 : x ≠ y := by parley_side
      parley_side
    · skip
      -- 2.2. inequalities
      have s2_2 : y ≠ x := by parley_side
      parley_side
  parley_side

end Parley.Tests.Elaborator.ACaseEndingOnItsClaimTurned.ACaseEndingOnItsClaimTurned
