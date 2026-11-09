module

public import InstanceTactics
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

namespace Parley.Tests.Elaborator.AForAllOverARange.AForAllOverAWiderSet

theorem a_for_all_over_a_wider_set (k : ℤ) (hH1 : 0 < k) (x : ℝ) (hH3 : True) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), ((j : ℝ) / x : ℝ)) = (∑ j ∈ Finset.Icc (1 : ℤ) k, ((j : ℝ) / x : ℝ)) + ((k : ℝ) + 1) / x := by
  -- 1. mun:sum-extended a := 1, n := k, from H3
  have r31_1 : k ≥ 1 := by parley_order
  have hI : (∑ b ∈ Finset.Icc (1 : ℤ) (k + 1), ((b : ℝ) / x : ℝ)) = (∑ b ∈ Finset.Icc (1 : ℤ) k, ((b : ℝ) / x : ℝ)) + ((k : ℝ) + 1) / x := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := k) r31_1))
  exact hI

end Parley.Tests.Elaborator.AForAllOverARange.AForAllOverAWiderSet
