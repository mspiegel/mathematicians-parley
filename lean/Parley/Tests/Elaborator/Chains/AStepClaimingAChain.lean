module

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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Chains.AStepClaimingAChain

theorem a_step_claiming_a_chain (x : ℝ) (y : ℝ) (z : ℝ) (hH4 : x = y) (hH5 : y = z) (hH6 : x + 1 = 5) :
    z + 1 = 5 := by
  -- 1. join H4, H5
  have s1 : x = y ∧ y = z := ⟨hH4, hH5⟩
  -- 2. substitute x = z (line 1) into H6
  exact Eq.subst (motive := (fun t : ℝ => t + 1 = 5)) (Eq.trans (s1.1) s1.2) hH6

end Parley.Tests.Elaborator.Chains.AStepClaimingAChain
