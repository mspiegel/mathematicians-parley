module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.ADivisorOfNumeralsBelowZero

theorem a_divisor_of_numerals_below_zero (c : ℤ) (x : ℝ) :
    x * (((c : ℝ) - (c : ℝ)) / (2 - 5)) = ((c : ℝ) - (c : ℝ)) / (2 - 5) * x := by
  -- 1. algebra
  ring1

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.ADivisorOfNumeralsBelowZero
