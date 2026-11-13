module

public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-supposition-written-otherwise.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.ASuppositionDenyingItsClaimWrittenOtherwise

theorem a_supposition_denying_its_claim_written_otherwise (a : ℝ) (hH2 : a = 1) :
    a = 1 := by
  -- 1. contradiction
  by_contra h_hS
  have hS : 1 ≠ a := Ne.symm h_hS
  -- 1.1. restate S
  have s1_1 : 1 ≠ a := by exact hS
  exact s1_1 hH2.symm

end Parley.Tests.Elaborator.ASuppositionWrittenOtherwise.ASuppositionDenyingItsClaimWrittenOtherwise
