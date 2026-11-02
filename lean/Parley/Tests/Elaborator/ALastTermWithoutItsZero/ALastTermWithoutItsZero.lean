module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-last-term-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALastTermWithoutItsZero.ALastTermWithoutItsZero

theorem a_last_term_without_its_zero :
    (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. mun:sum-last n := 0, from 1
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ALastTermWithoutItsZero.ALastTermWithoutItsZero
