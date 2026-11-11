module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ExponentNegative

theorem exponent_negative (a : ℝ) (hH2 : a ≠ 0) (m : ℤ) :
    a ^ (-m) = 1 / a ^ m := by
  -- 1. mun:numbers-exponent-negative, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) hH2 (m := m))

end Parley.Tests.Stdlib.Numbers.ExponentNegative
