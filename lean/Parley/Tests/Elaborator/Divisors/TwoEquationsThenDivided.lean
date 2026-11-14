module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
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

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.TwoEquationsThenDivided

theorem two_equations_then_divided (x : ℝ) (y : ℝ) (z : ℝ) (hH4 : y = 1) (hH5 : z = 2) (hH6 : x + 3 ≠ 0) :
    (x * y + z) / (x + 3) = (x + 2) / (x + 3) := by
  -- 1. algebra, from H4, H5
  have r69_1 : x + 3 ≠ 0 := by exact hH6
  have hz1 : x + 3 ≠ 0 := r69_1; linear_combination (norm := (field)) ((x) / ((x + 3))) * hH4 + ((1) / ((x + 3))) * hH5

end Parley.Tests.Elaborator.Divisors.TwoEquationsThenDivided
