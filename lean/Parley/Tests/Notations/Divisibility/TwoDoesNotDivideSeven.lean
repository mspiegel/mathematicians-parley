module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.TwoDoesNotDivideSeven

theorem two_does_not_divide_seven :
    ¬ (2 : ℤ) ∣ (7 : ℤ) := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Divisibility.TwoDoesNotDivideSeven
