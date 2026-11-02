module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-sum-dividing-by-a-positive-index.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumDividingByAPositiveIndex.ASumDividingByAPositiveIndex

theorem a_sum_dividing_by_a_positive_index (n : ℕ) (hH1 : 0 < n) (hH2 : ∀ k : ℤ, k ∈ Finset.Icc 1 (n : ℤ) → 0 ≤ 1 / (k : ℚ)) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (0 : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / (k : ℚ) : ℚ)) := by
  -- 1. mun:sum-le a := 1, b := n, from H2
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (0 : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / (k : ℚ) : ℚ)) := by first | linarith [(Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (0 : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (0 : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (0 : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (0 : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ASumDividingByAPositiveIndex.ASumDividingByAPositiveIndex
