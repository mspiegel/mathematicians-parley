module

public import Roots
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

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmBelowOne

theorem a_logarithm_below_one :
    Real.log (2 : ℝ) < 1 := by
  -- 1. real arithmetic
  have hf1 : (5 / 8 : ℝ) < Real.log (2 : ℝ) := by exact_mod_cast Roots.log_above (p := 2) (a := 5) (b := 8) (by norm_num) (by norm_num) (by norm_num)
  have hf2 : Real.log (2 : ℝ) < (1 / 1 : ℝ) := by exact_mod_cast Roots.log_below (p := 2) (a := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith only [hf1, hf2]

end Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmBelowOne
