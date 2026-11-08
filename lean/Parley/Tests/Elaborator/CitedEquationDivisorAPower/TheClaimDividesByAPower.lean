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

/-! Written from tests/elaborator/cited-equation-divisor-a-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitedEquationDivisorAPower.TheClaimDividesByAPower

theorem the_claim_divides_by_a_power (t : ℝ) (F : ℝ) (hH3 : t ≠ 0) (hH4 : F * t ^ 2 = 1) :
    F = 1 / t ^ 2 := by
  -- 1. algebra, from H4
  have r26_1 : t ≠ 0 := by parley_side
  linear_combination (norm := parley_field) ((1) / ((t ^ 2))) * hH4

end Parley.Tests.Elaborator.CitedEquationDivisorAPower.TheClaimDividesByAPower
