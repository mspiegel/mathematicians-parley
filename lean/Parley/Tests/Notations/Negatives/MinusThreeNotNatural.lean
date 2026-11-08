module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusThreeNotNatural

theorem minus_three_not_natural :
    ¬ (0 : ℤ) ≤ -3 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusThreeNotNatural
