module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.TwoLogarithmsThatDiffer

theorem two_logarithms_that_differ :
    Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
  -- 1. real arithmetic
  have hf1 : Real.log (2 / 3 : ℝ) = Real.log (2 : ℝ) - Real.log (3 : ℝ) := by rw [Real.log_div (show (2 : ℝ) ≠ 0 by norm_num) (show (3 : ℝ) ≠ 0 by norm_num)]
  intro h
  exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < (2 / 3 : ℝ) by norm_num) (show (2 / 3 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1)

end Parley.Tests.Elaborator.RealArithmeticLogarithms.TwoLogarithmsThatDiffer
