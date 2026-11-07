module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.ADivisorOfNumeralsBelowZero

theorem a_divisor_of_numerals_below_zero (c : ℤ) (x : ℝ) :
    x * (((c : ℝ) - (c : ℝ)) / (2 - 5)) = ((c : ℝ) - (c : ℝ)) / (2 - 5) * x := by
  -- 1. algebra
  have s1 : x * (((c : ℝ) - (c : ℝ)) / (2 - 5)) = ((c : ℝ) - (c : ℝ)) / (2 - 5) * x := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.ADivisorOfNumeralsBelowZero
