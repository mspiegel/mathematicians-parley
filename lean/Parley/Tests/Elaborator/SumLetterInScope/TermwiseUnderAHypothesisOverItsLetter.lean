module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/sum-letter-in-scope.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SumLetterInScope.TermwiseUnderAHypothesisOverItsLetter

theorem termwise_under_a_hypothesis_over_its_letter (n : ℤ) (hH1 : 0 < n) (hH2 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (k : ℤ)) ≥ 0) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (k + 0 : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (k : ℤ)) := by
  -- 1. proof
  have s1 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → k + 0 = k := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 1.1. algebra
    parley_ring
  -- 2. mun:sum-termwise a := 1, b := n, from 1
  exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := n) s1)

end Parley.Tests.Elaborator.SumLetterInScope.TermwiseUnderAHypothesisOverItsLetter
