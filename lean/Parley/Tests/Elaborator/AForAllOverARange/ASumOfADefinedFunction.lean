module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-for-all-over-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllOverARange.ASumOfADefinedFunction

theorem a_sum_of_a_defined_function (k : ℤ) (hH1 : 0 < k) (x : ℝ) (hH3 : x > 0) (t : ℤ → ℝ) (hD1 : ∀ j : ℤ, 0 < j → t j = (j : ℝ) / x) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (t j : ℝ)) = (∑ j ∈ Finset.Icc (1 : ℤ) k, (t j : ℝ)) + t (k + 1) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. mun:sum-extended a := 1, n := k
  have r52_1 : k ≥ 1 := by parley_order
  exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := k) r52_1)

end Parley.Tests.Elaborator.AForAllOverARange.ASumOfADefinedFunction
