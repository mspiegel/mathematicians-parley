module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusOfMinus

theorem minus_of_minus :
    (-(-3) : ℤ) = 3 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusOfMinus
