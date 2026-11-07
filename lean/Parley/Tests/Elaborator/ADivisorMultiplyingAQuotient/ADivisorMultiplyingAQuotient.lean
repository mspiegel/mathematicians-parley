module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-divisor-multiplying-a-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADivisorMultiplyingAQuotient.ADivisorMultiplyingAQuotient

theorem a_divisor_multiplying_a_quotient (s : ℂ) (T : ℂ) (hH3 : s ^ 2 = 4) (hH4 : s ≠ 0) (hH5 : T ≠ 0) :
    1 / (s / 2 * T) = s / (2 * T) := by
  -- 1. algebra, from H3, H4, H5
  have s1 : 1 / (s / 2 * T) = s / (2 * T) := by linear_combination (norm := parley_field) ((-(1 / 2 : ℂ)) / ((T * s))) * hH3
  all_goals exact s1

end Parley.Tests.Elaborator.ADivisorMultiplyingAQuotient.ADivisorMultiplyingAQuotient
