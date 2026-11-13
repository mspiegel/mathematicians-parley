module

public import RealTactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.TwoLogarithmsThatDiffer

theorem two_logarithms_that_differ :
    Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmeticLogarithms.TwoLogarithmsThatDiffer
