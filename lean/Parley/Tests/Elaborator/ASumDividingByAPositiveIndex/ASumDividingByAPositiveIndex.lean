module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-sum-dividing-by-a-positive-index.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumDividingByAPositiveIndex.ASumDividingByAPositiveIndex

theorem a_sum_dividing_by_a_positive_index (n : ℤ) (hH1 : 0 < n) (hH2 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → 0 ≤ 1 / (k : ℚ)) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (0 : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℚ) : ℚ)) := by
  -- 1. mun:sum-le a := 1, b := n, from H2
  exact (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (0 : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := n) hH2)

end Parley.Tests.Elaborator.ASumDividingByAPositiveIndex.ASumDividingByAPositiveIndex
