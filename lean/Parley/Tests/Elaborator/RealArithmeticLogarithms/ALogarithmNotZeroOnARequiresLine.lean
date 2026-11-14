module

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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmNotZeroOnARequiresLine

theorem a_logarithm_not_zero_on_a_requires_line (a : ℝ) :
    a * Real.log (2 : ℝ) / Real.log (2 : ℝ) = a := by
  -- 1. algebra
  have r83_1 : Real.log (2 : ℝ) ≠ 0 := by
    have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
    intro h
    exact Real.log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num) (by linear_combination h + hf1)
  have hz1 : Real.log (2 : ℝ) ≠ 0 := r83_1; field

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmNotZeroOnARequiresLine
