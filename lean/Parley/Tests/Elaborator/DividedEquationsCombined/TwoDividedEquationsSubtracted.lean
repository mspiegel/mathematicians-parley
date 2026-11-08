module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divided-equations-combined.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DividedEquationsCombined.TwoDividedEquationsSubtracted

theorem two_divided_equations_subtracted (A : ℝ) (B : ℝ) (p : ℤ) (q : ℤ) (hH4 : 0 < q) (r : ℤ) (s : ℤ) (hH6 : 0 < s) (hH7 : A + B = (p : ℝ) / (q : ℝ)) (hH8 : B = (r : ℝ) / (s : ℝ)) :
    A = (p : ℝ) / (q : ℝ) - (r : ℝ) / (s : ℝ) := by
  -- 1. algebra, from H7, H8
  linear_combination (norm := parley_field) hH7 + (-1) * hH8

end Parley.Tests.Elaborator.DividedEquationsCombined.TwoDividedEquationsSubtracted
