module

public import Logarithms
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowALogarithm

theorem one_below_a_logarithm :
    1 < Real.log (3 : ℝ) := by
  -- 1. real arithmetic
  have hf1 : (1 / 1 : ℝ) < Real.log (3 : ℝ) := by exact_mod_cast LeanBridges.Logarithms.log_above (p := 3) (a := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  have hf2 : Real.log (3 : ℝ) < (8 / 5 : ℝ) := by exact_mod_cast LeanBridges.Logarithms.log_below (p := 3) (a := 8) (b := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith only [hf1, hf2]

end Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowALogarithm
