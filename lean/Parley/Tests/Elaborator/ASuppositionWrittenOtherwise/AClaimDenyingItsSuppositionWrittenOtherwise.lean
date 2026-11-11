module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/a-supposition-written-otherwise.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.AClaimDenyingItsSuppositionWrittenOtherwise

theorem a_claim_denying_its_supposition_written_otherwise (a : ℝ) (hH2 : a ≠ 1) :
    a ≠ 1 := by
  -- 1. contradiction
  intro h_hS
  have hS : 1 = a := h_hS.symm
  -- 1.1. restate S
  have s1_1 : 1 = a := by exact hS
  exact hH2 s1_1.symm

end Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.AClaimDenyingItsSuppositionWrittenOtherwise
