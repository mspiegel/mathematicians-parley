module

public import AlgebraTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
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

/-! Written from tests/elaborator/cited-equation-divisor-a-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitedEquationDivisorAPower.ACitedEquationDividesByAPower

theorem a_cited_equation_divides_by_a_power (t : ℝ) (F : ℝ) (hH3 : t ≠ 0) (hH4 : F = 1 / t ^ 2) :
    F * t ^ 2 = 1 := by
  -- 1. algebra, from H4
  have r12_1 : t ≠ 0 := by exact hH3
  linear_combination (norm := parley_field) (t ^ 2) * hH4

end Parley.Tests.Elaborator.CitedEquationDivisorAPower.ACitedEquationDividesByAPower
