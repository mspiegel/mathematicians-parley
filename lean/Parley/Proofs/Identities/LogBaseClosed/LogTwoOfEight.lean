module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from proofs/identities/log-base-closed.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight

theorem log_two_of_eight :
    Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 := by
  -- 1. substitute ln(8) = 3·ln(2) (real arithmetic)
  have s1 : Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by
    have e_real : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
      have hv1 : Real.log (8 : ℝ) = ((3 : ℕ) : ℝ) * Real.log (2 : ℝ) := by rw [congrArg Real.log (show (8 : ℝ) = 2 ^ 3 by ring1), Real.log_pow 2 3]
      linear_combination hv1
    exact congrArg (fun t : ℝ => t / Real.log (2 : ℝ)) e_real
  -- 2. calculation
  have r11_1 : Real.log (2 : ℝ) ≠ 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    intro h
    exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1)
  calc Real.log (8 : ℝ) / Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) / Real.log (2 : ℝ) := s1
    _ = 3 := by have hz1 : Real.log (2 : ℝ) ≠ 0 := r11_1; field

end Parley.Proofs.Identities.LogBaseClosed.LogTwoOfEight
