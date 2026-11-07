module

public import ArithTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/a-supposition-written-otherwise.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.ASuppositionDenyingItsClaimWrittenOtherwise

theorem a_supposition_denying_its_claim_written_otherwise (a : ℝ) (hH2 : a = 1) :
    a = 1 := by
  -- 1. contradiction
  have s1 : a = 1 := by
    by_contra hc_hS
    have hS : 1 ≠ a := by parley_suppose hc_hS
    -- 1.1. restate S
    have s1_1 : 1 ≠ a := by parley_side
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.ASuppositionDenyingItsClaimWrittenOtherwise
