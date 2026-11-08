module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusPlus

theorem minus_plus :
    (-3 + 5 : ℤ) = 2 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusPlus
