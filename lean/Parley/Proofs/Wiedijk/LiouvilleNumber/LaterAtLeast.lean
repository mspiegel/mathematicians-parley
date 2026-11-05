module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtLeast

theorem later_at_least (n : ℕ) (hH1 : 0 < n) :
    (∀ i : ℕ, 0 < i → (i : ℤ) ≥ (n : ℤ) + 1 → (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (i : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) := by
  -- 1. thm:partial-sums-increase n := n + 1
  have s1 : ∀ j : ℕ, (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1 + (j : ℤ)), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by first | exact (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease.partial_sums_increase (n := n + 1) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease.partial_sums_increase (n := n + 1) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease.partial_sums_increase (n := n + 1) (by parley_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease.partial_sums_increase (n := n + 1) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease.partial_sums_increase (n := n + 1) (by parley_side)); parley_side)
  -- 2. proof
  have s2 : ∀ i : ℕ, 0 < i → (i : ℤ) ≥ (n : ℤ) + 1 → (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (i : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
    intro i hK
    intro hA
    -- 2.1. mun:difference-nat0 m := n + 1, n := i, from A
    have s2_1 : 0 ≤ (i : ℤ) - ((n : ℤ) + 1) := by first | exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := n + 1) (n := i) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := n + 1) (n := i) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := n + 1) (n := i) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := n + 1) (n := i) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := n + 1) (n := i) (by parley_side)); parley_side)
    -- 2.2. instantiate j := i − (n + 1) in line 1, from 2.1
    have s2_2 : (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1 + ((i : ℤ) - ((n : ℤ) + 1))), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by have h := (s1 ((i : ℤ) - ((n : ℤ) + 1)).toNat); rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((i : ℤ) - ((n : ℤ) + 1)) by parley_side)] at h; exact h
    -- 2.3. substitute
    have s2_3 : (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (i : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
      have c1 : (n : ℤ) + 1 + ((i : ℤ) - ((n : ℤ) + 1)) = (i : ℤ) := by parley_ring
      have c1_w : (n : ℚ) + 1 + ((i : ℚ) - ((n : ℚ) + 1)) = (i : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
      have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (i : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by first | parley_subst_at c1_w s2_2 | parley_subst_at c1 s2_2
      exact row1
    all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtLeast
