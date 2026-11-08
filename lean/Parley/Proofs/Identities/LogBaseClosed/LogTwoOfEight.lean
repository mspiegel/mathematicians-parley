module

public import AlgebraTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/identities/log-base-closed.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight

theorem log_two_of_eight :
    Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 := by
  -- 1. substitute ln(8) = 3·ln(2) (real arithmetic)
  have s1 : Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by parley_subst (show Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) by parley_real)
  -- 2. calculation
  have r11_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  calc Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by parley_side
    _ = 3 := by parley_ring

end Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight
