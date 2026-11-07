module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.RemainderOfAPower

theorem remainder_of_a_power :
    (10 ^ 3 : ℤ) % (7 : ℤ) = 6 := by
  -- 1. arithmetic
  have s1 : (10 ^ 3 : ℤ) % (7 : ℤ) = 6 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.RemainderOfAPower
