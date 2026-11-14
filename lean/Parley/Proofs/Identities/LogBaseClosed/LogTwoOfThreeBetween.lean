module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
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
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/log-base-closed.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseClosed.LogTwoOfThreeBetween

theorem log_two_of_three_between :
    (1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) ∧ Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2) := by
  -- 1. mun:quotient-positive x := ln(3) − ln(2), y := ln(2)
  have r37_1 : Real.log (3 : ℝ) - Real.log (2 : ℝ) > 0 := by
    have hf1 : Real.log (3 / 2 : ℝ) = -Real.log (2 : ℝ) + Real.log (3 : ℝ) := by rw [Real.log_div (show (3 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ≠ 0 by norm_num)]; ring1
    have hf2 : (0 : ℝ) < Real.log (3 / 2 : ℝ) := Real.log_pos (show (1 : ℝ) < (3 / 2 : ℝ) by norm_num)
    linarith only [hf1, hf2]
  have r37_2 : Real.log (2 : ℝ) > 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    have hf2 : (0 : ℝ) < Real.log (2 : ℝ) := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith only [hf1, hf2]
  have s1 : (Real.log (3 : ℝ) - Real.log (2 : ℝ)) / Real.log (2 : ℝ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ) - Real.log (2 : ℝ)) (y := Real.log (2 : ℝ)) r37_1 r37_2)
  -- 2. substitute
  have r42_1 : Real.log (2 : ℝ) ≠ 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    intro h
    exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1)
  have s2 : Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 > 0 := by
    have c1 : (Real.log (3 : ℝ) - Real.log (2 : ℝ)) / Real.log (2 : ℝ) = Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 := by field
    have row1 : Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 > 0 := Eq.subst (motive := (fun t : ℝ => t > 0)) c1 s1
    exact row1
  -- 3. inequalities, from 2
  have r48_1 : Real.log (2 : ℝ) ≠ 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    intro h
    exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1)
  have s3 : 1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) := by linarith only [s2]
  -- 4. mun:quotient-positive x := 2·ln(2) − ln(3), y := ln(2)
  have r52_1 : 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) > 0 := by
    have hf1 : Real.log (4 / 3 : ℝ) = 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by rw [congrArg Real.log (show (4 / 3 : ℝ) = 2 ^ 2 / 3 by ring1), Real.log_div (show (2 ^ 2 : ℝ) ≠ 0 by norm_num) (show (3 : ℝ) ≠ 0 by norm_num), Real.log_pow 2 2]; ring1
    have hf2 : (0 : ℝ) < Real.log (4 / 3 : ℝ) := Real.log_pos (show (1 : ℝ) < (4 / 3 : ℝ) by norm_num)
    linarith only [hf1, hf2]
  have r52_2 : Real.log (2 : ℝ) > 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    have hf2 : (0 : ℝ) < Real.log (2 : ℝ) := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith only [hf1, hf2]
  have s4 : (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) / Real.log (2 : ℝ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) r52_1 r52_2)
  -- 5. substitute
  have r57_1 : Real.log (2 : ℝ) ≠ 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    intro h
    exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1)
  have s5 : 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := by
    have c1 : (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) / Real.log (2 : ℝ) = 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) := by field
    have row1 : 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := Eq.subst (motive := (fun t : ℝ => t > 0)) c1 s4
    exact row1
  -- 6. inequalities
  have r63_1 : Real.log (2 : ℝ) ≠ 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    intro h
    exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1)
  have s6 : Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2 := by linarith only [s5]
  -- 7. join 3, 6
  have s7 : 1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) ∧ Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2 := ⟨s3, s6⟩
  exact ⟨(s7).1, (s7).2⟩

end Parley.Proofs.Identities.LogBaseClosed.LogTwoOfThreeBetween
