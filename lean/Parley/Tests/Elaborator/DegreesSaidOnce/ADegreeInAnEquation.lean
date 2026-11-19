module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/degrees-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DegreesSaidOnce.ADegreeInAnEquation

theorem a_degree_in_an_equation (x : ℝ) (hH2 : 2 * x = (90 : ℝ) * Real.pi / 180) :
    x = (45 : ℝ) * Real.pi / 180 := by
  -- 1. algebra, from H2
  linear_combination ((16200) / ((180) * (180))) * hH2

end Parley.Tests.Elaborator.DegreesSaidOnce.ADegreeInAnEquation
