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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.TwoToTheTenth

theorem two_to_the_tenth :
    (2 ^ 10 : ℤ) = 1024 := by
  -- 1. arithmetic
  have s1 : (2 ^ 10 : ℤ) = 1024 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Numbers.TwoToTheTenth
