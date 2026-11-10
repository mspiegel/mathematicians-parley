module

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
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-for-all-over-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllOverARange.AForAllReadAtANumeral

theorem a_for_all_read_at_a_numeral (x : ℝ) (hH2 : x > 0) (t : ℤ → ℝ) (hD1 : ∀ j : ℤ, 0 < j → t j = (j : ℝ) / x) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (t j : ℝ)) = t 1 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. mun:sum-single a := 1
  exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ)))

end Parley.Tests.Elaborator.AForAllOverARange.AForAllReadAtANumeral
