module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.TwentyThreeFactorsAsAFraction

theorem twenty_three_factors_as_a_fraction :
    (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - (k : ℚ) : ℚ)) / 365 ^ 23 < 1 / 2 := by
  -- 1. arithmetic
  have s1 : (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - (k : ℚ) : ℚ)) / 365 ^ 23 < 1 / 2 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.TwentyThreeFactorsAsAFraction
