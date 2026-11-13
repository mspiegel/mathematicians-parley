module

public import ArithTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusThreeNotNatural

theorem minus_three_not_natural :
    ¬ (0 : ℤ) ≤ -3 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusThreeNotNatural
