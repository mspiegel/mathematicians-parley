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
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/cited-equation-divisor-a-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitedEquationDivisorAPower.ThePowerSaidNotZeroWhole

theorem the_power_said_not_zero_whole (t : ℝ) (F : ℝ) (hH3 : t ≠ 0) (hH4 : F = 1 / t ^ 2) :
    F * t ^ 2 = 1 := by
  -- 1. mun:square-positive x := t, from H3
  have s1 : t ^ 2 > 0 := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := t) (by parley_side))
  -- 2. algebra, from H4
  have r42_1 : t ^ 2 ≠ 0 := by parley_side
  linear_combination (norm := parley_field) (t ^ 2) * hH4

end Parley.Tests.Elaborator.CitedEquationDivisorAPower.ThePowerSaidNotZeroWhole
