module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SevenModThree

theorem seven_mod_three :
    (7 : ℤ) % (3 : ℤ) = 1 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Numbers.SevenModThree
