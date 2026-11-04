module

public import AlgebraTactics
public import Counting
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum

/-! Written from proofs/hammack/weighted-binomial-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialSum.WeightedBinomialSum

theorem weighted_binomial_sum (n : ℕ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) : ℚ)) = (n : ℚ) * 2 ^ ((n : ℤ) - 1) := by
  -- 1. thm:weighted-row-sum m := n − 1
  have r172_1 : 0 ≤ (n : ℤ) - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)); parley_side)
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1 + 1), ((k : ℚ) * (LeanBridges.Counting.choose ((n : ℤ) - 1 + 1) k : ℚ) : ℚ)) = ((n : ℚ) - 1 + 1) * 2 ^ ((n : ℤ) - 1) := by first | linear_combination (norm := parley_norm) (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); exact_mod_cast h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); rify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); qify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); parley_int_power h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - 1) by parley_side) ▸ (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := ((n : ℤ) - 1).toNat))); parley_side)
  -- 2. substitute
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) : ℚ)) = (n : ℚ) * 2 ^ ((n : ℤ) - 1) := by
    have c1 : (n : ℤ) - 1 + 1 = (n : ℤ) := by parley_ring
    have c1_w : (n : ℚ) - 1 + 1 = (n : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
    have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) : ℚ)) = (n : ℚ) * 2 ^ ((n : ℤ) - 1) := by first | parley_subst_at c1_w s1 | parley_subst_at c1 s1
    exact row1
  all_goals exact s2

end Parley.Proofs.Hammack.WeightedBinomialSum.WeightedBinomialSum
