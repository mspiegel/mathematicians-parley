module

public import AlgebraTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-divisor-negating-a-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADivisorNegatingAQuotient.AnAbsoluteValueOverItsNegation

theorem an_absolute_value_over_its_negation (p : ℝ) (hH2 : abs (p / 2) = p / 2) (hH3 : abs (-(p / 2)) = abs (p / 2)) (hH4 : -(p / 2) ≠ 0) :
    abs (-(p / 2)) / -(p / 2) = -1 := by
  -- 1. algebra, from H2, H3
  have r22_1 : -(p / 2) ≠ 0 := by exact hH4
  linear_combination (norm := parley_field) ((4) / ((-p) * (2))) * hH2 + ((2) / ((-p))) * hH3

end Parley.Tests.Elaborator.ADivisorNegatingAQuotient.AnAbsoluteValueOverItsNegation
