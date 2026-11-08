module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusTimesMinus

theorem minus_times_minus :
    (-1 * -1 : ℤ) = 1 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusTimesMinus
