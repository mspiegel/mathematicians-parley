module

public import NormTactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.AMultiplierOfTwoTerms

theorem a_multiplier_of_two_terms (x : ℝ) (y : ℝ) (hH3 : y = 1) :
    x ^ 2 * y - x * y + 2 = x ^ 2 - x + 2 := by
  -- 1. algebra, from H3
  linear_combination (norm := parley_norm) (x ^ 2 - x) * hH3

end Parley.Tests.Elaborator.Combinations.AMultiplierOfTwoTerms
