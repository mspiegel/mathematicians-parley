module

public import AlgebraTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-sum-lemma-over-another-bound-letter.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumLemmaOverAnotherBoundLetter.ASumTermwiseOverAnotherLetter

theorem a_sum_termwise_over_another_letter (n : ℤ) (hH1 : 0 < n) :
    (∑ j ∈ Finset.Icc (1 : ℤ) n, (j + j : ℤ)) = (∑ j ∈ Finset.Icc (1 : ℤ) n, (2 * j : ℤ)) := by
  -- 1. algebra
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → i + i = 2 * i := by intro i h_i; parley_ring
  -- 2. membership
  -- 3. membership
  -- 4. mun:sum-termwise a := 1, b := n, from 1, 2, 3
  have s4 : (∑ j ∈ Finset.Icc (1 : ℤ) n, (j + j : ℤ)) = (∑ j ∈ Finset.Icc (1 : ℤ) n, (2 * j : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) (by parley_side)); parley_side)
  all_goals exact s4

end Parley.Tests.Elaborator.ASumLemmaOverAnotherBoundLetter.ASumTermwiseOverAnotherLetter
