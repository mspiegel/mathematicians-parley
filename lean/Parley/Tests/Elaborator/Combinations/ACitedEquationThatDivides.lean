module

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

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.ACitedEquationThatDivides

theorem a_cited_equation_that_divides (x : ℝ) (y : ℝ) (hH3 : (x + y) / 2 = 2) :
    1 / 2 * (x * y) + 1 / 2 * y ^ 2 + y = 3 * y := by
  -- 1. algebra, from H3
  linear_combination ((8 * y) / ((4) * ((2 : ℝ)))) * hH3

end Parley.Tests.Elaborator.Combinations.ACitedEquationThatDivides
