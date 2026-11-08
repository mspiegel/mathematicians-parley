module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual

theorem fractions_equal :
    (2 / 4 : ℚ) ≤ 3 / 6 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual
