module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.ASumOverARangeWrittenAsASet

theorem a_sum_over_a_range_written_as_a_set (n : ℤ) (hH1 : 0 < n) (t : ℤ → ℝ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (t k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) + t (n + 1) := by
  -- 1. mun:sum-extended a := 1
  have r129_1 : n ≥ 1 := by parley_side
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (t k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) + t (n + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Sums.ASumOverARangeWrittenAsASet
