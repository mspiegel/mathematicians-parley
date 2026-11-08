module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.FractionsApart

theorem fractions_apart :
    (17 / (3 * 2) / 65 : ℚ) ≠ 2 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.ClosedValues.FractionsApart
