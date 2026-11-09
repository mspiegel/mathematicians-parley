module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/empty-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.EmptySum.EmptySum

theorem empty_sum (B : ℤ → ℝ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (B k : ℝ)) = 0 := by
  -- 1. mun:sum-single a := 0
  have s1 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (B k : ℝ)) = B 0 := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ)))
  -- 2. mun:sum-first n := 0
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (B k : ℝ)) = B 0 + (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (B k : ℝ)) := by simpa only [zero_add] using (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side))
  -- 3. algebra, from 1, 2
  linear_combination (norm := parley_norm) s1 + (-1) * s2

end Parley.Proofs.Setmm.EmptySum.EmptySum
