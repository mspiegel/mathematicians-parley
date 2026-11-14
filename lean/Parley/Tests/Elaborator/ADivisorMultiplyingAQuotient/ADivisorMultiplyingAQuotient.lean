module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-divisor-multiplying-a-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADivisorMultiplyingAQuotient.ADivisorMultiplyingAQuotient

theorem a_divisor_multiplying_a_quotient (s : ℂ) (T : ℂ) (hH3 : s ^ 2 = 4) (hH4 : s ≠ 0) (hH5 : T ≠ 0) :
    1 / (s / 2 * T) = s / (2 * T) := by
  -- 1. algebra, from H3, H4, H5
  have hz1 : s ≠ 0 := hH4; have hz2 : T ≠ 0 := hH5; linear_combination (norm := (field)) ((-(1 / 2 : ℂ)) / ((s) * ((1 / 2 : ℂ)) * (2 * T))) * hH3

end Parley.Tests.Elaborator.ADivisorMultiplyingAQuotient.ADivisorMultiplyingAQuotient
