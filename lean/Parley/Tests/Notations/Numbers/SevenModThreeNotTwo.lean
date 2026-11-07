module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SevenModThreeNotTwo

theorem seven_mod_three_not_two :
    (7 : ℤ) % (3 : ℤ) ≠ 2 := by
  -- 1. arithmetic
  have s1 : (7 : ℤ) % (3 : ℤ) ≠ 2 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Numbers.SevenModThreeNotTwo
