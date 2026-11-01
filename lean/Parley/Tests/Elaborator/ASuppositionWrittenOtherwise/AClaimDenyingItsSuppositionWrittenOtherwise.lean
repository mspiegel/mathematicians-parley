module

public import Parley.Library

/-! Written from tests/elaborator/a-supposition-written-otherwise.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.AClaimDenyingItsSuppositionWrittenOtherwise

theorem a_claim_denying_its_supposition_written_otherwise (a : ℝ) (H2 : a ≠ 1) :
    a ≠ 1 := by
  -- 1. contradiction
  have s1 : a ≠ 1 := by
    by_contra hc_S
    have S : 1 = a := by parley_suppose hc_S
    -- 1.1. restate S
    have s1_1 : 1 = a := by parley_side
    parley_side
  parley_side

end Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.AClaimDenyingItsSuppositionWrittenOtherwise
