module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-named-value-of-a-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamedValueOfAFunction.ANamedValueOfAFunction

theorem a_named_value_of_a_function (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) :
    a k ^ 2 ≥ 0 := by
  set x : ℝ := a k with hD1
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 2. calculation
  calc a k ^ 2 = x ^ 2 := by simp (disch := omega) only [hD1]
    _ ≥ 0 := s1

end Parley.Tests.Elaborator.ANamedValueOfAFunction.ANamedValueOfAFunction
