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

namespace Parley.Proofs.Identities.LogBaseClosed.LogTenOfThousand

theorem log_ten_of_thousand :
    Real.log (1000 : ℝ) / Real.log (10 : ℝ) = 3 := by
  -- 1. substitute ln(1000) = 3·ln(10) (real arithmetic)
  have s1 : Real.log (1000 : ℝ) / Real.log (10 : ℝ) = 3 * Real.log (10 : ℝ) / Real.log (10 : ℝ) := by
    have e_real : Real.log (1000 : ℝ) = 3 * Real.log (10 : ℝ) := by
      have hv1 : Real.log (10 : ℝ) = Real.log (2 : ℝ) + Real.log (5 : ℝ) := by rw [congrArg Real.log (show (10 : ℝ) = 2 * 5 by ring1), Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (5 : ℝ) ≠ 0 by norm_num)]
      have hv2 : Real.log (1000 : ℝ) = ((3 : ℕ) : ℝ) * Real.log (2 : ℝ) + ((3 : ℕ) : ℝ) * Real.log (5 : ℝ) := by rw [congrArg Real.log (show (1000 : ℝ) = 2 ^ 3 * 5 ^ 3 by ring1), Real.log_mul (show (2 ^ 3 : ℝ) ≠ 0 by norm_num) (show (5 ^ 3 : ℝ) ≠ 0 by norm_num), Real.log_pow 2 3, Real.log_pow 5 3]
      linear_combination (-3) * hv1 + hv2
    exact congrArg (fun t : ℝ => t / Real.log (10 : ℝ)) e_real
  -- 2. calculation
  have r25_1 : Real.log (10 : ℝ) ≠ 0 := by
    have hv1 : Real.log (10 : ℝ) = Real.log (2 : ℝ) + Real.log (5 : ℝ) := by rw [congrArg Real.log (show (10 : ℝ) = 2 * 5 by ring1), Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (5 : ℝ) ≠ 0 by norm_num)]
    have hf1 : Real.log (10 : ℝ) = Real.log (2 : ℝ) + Real.log (5 : ℝ) := by rw [congrArg Real.log (show (10 : ℝ) = 2 * 5 by ring1), Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (5 : ℝ) ≠ 0 by norm_num)]
    intro h
    exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < 10 by norm_num) (show (10 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1 + (-1) * hv1)
  calc Real.log (1000 : ℝ) / Real.log (10 : ℝ) = 3 * Real.log (10 : ℝ) / Real.log (10 : ℝ) := s1
    _ = 3 := by have hz1 : Real.log (10 : ℝ) ≠ 0 := r25_1; field

end Parley.Proofs.Identities.LogBaseClosed.LogTenOfThousand
