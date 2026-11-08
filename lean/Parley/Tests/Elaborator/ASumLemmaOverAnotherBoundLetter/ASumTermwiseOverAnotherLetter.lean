module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
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
  exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun j : ℤ => j + j)) (u := (fun j : ℤ => 2 * j)) (a := (1 : ℤ)) (b := n) s1)

end Parley.Tests.Elaborator.ASumLemmaOverAnotherBoundLetter.ASumTermwiseOverAnotherLetter
