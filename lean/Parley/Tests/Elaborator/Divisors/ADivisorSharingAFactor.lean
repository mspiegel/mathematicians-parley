module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.ADivisorSharingAFactor

theorem a_divisor_sharing_a_factor (x : ℝ) (y : ℝ) (z : ℝ) (hH4 : y ^ 2 = 9) (hH5 : y - 3 ≠ 0) :
    (x * y ^ 2 - 2 * y ^ 2 - z) / (y - 3) = (9 * x - z - 18) / (y - 3) := by
  -- 1. algebra, from H4
  have r83_1 : y - 3 ≠ 0 := by parley_side
  have s1 : (x * y ^ 2 - 2 * y ^ 2 - z) / (y - 3) = (9 * x - z - 18) / (y - 3) := by linear_combination (norm := parley_field) ((x - 2) / ((y - 3))) * hH4
  all_goals exact s1

end Parley.Tests.Elaborator.Divisors.ADivisorSharingAFactor
