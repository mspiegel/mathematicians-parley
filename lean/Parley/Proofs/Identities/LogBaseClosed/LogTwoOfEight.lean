module

public import RealTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
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

/-! Written from proofs/identities/log-base-closed.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight

theorem log_two_of_eight :
    Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 := by
  -- 1. substitute ln(8) = 3·ln(2) (real arithmetic)
  have s1 : Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by
    have e_real : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by parley_real
    exact congrArg (fun t : ℝ => t / Real.log (2 : ℝ)) e_real
  -- 2. calculation
  have r11_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  calc Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := s1
    _ = 3 := by have hz1 : Real.log (2 : ℝ) ≠ 0 := r11_1; field

end Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight
