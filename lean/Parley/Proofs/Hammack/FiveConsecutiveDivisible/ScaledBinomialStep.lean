module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm

/-! Written from proofs/hammack/five-consecutive-divisible.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep

theorem scaled_binomial_step (m : ℕ) (i : ℕ) (j : ℕ) (hH3 : 0 < j) (hH4 : (j : ℤ) - 1 = (i : ℤ)) :
    (j : ℤ) * (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ)) (j : ℤ) : ℤ) = ((m : ℤ) + (j : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (i : ℤ)) (i : ℤ) : ℤ) := by
  -- 1. inequalities
  have s1 : (j : ℤ) = (i : ℤ) + 1 := by parley_side
  -- 2. inequalities, from H1
  have s2 : (i : ℤ) + 1 ≤ (m : ℤ) + (i : ℤ) + 1 := by parley_order
  -- 3. transitivity, from 1, 2
  have s3 : (j : ℤ) ≤ (m : ℤ) + (i : ℤ) + 1 := by parley_order
  -- 4. def:range-between k := j, a := 1, b := (m + i) + 1, from 3
  have r33_1 : 1 ≤ (j : ℤ) := by parley_order
  have s4 : (j : ℤ) ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + (i : ℤ) + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (j : ℤ)) (a := (1 : ℤ)) (b := (m : ℤ) + (i : ℤ) + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (j : ℤ)) (a := (1 : ℤ)) (b := (m : ℤ) + (i : ℤ) + 1))).mpr (by parley_side); parley_side)
  -- 5. thm:weighted-term m := m + i, k := j, from 4
  have s5 : (j : ℤ) * (LeanBridges.Counting.choose ((m : ℤ) + (i : ℤ) + 1) (j : ℤ) : ℤ) = ((m : ℤ) + (i : ℤ) + 1) * (LeanBridges.Counting.choose ((m : ℤ) + (i : ℤ)) ((j : ℤ) - 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (k := (j : ℤ)) (by parley_side)); parley_side)
  -- 6. substitute j − 1 = i (H4) into line 5
  have s6 : (j : ℤ) * (LeanBridges.Counting.choose ((m : ℤ) + (i : ℤ) + 1) (j : ℤ) : ℤ) = ((m : ℤ) + (i : ℤ) + 1) * (LeanBridges.Counting.choose ((m : ℤ) + (i : ℤ)) (i : ℤ) : ℤ) := by parley_subst_at hH4 s5
  -- 7. algebra, from 1
  have s7 : (m : ℤ) + (i : ℤ) + 1 = (m : ℤ) + (j : ℤ) := by linear_combination (norm := parley_norm) (-1) * s1
  -- 8. substitute (m + i) + 1 = m + j (line 7) into line 6
  have s8 : (j : ℤ) * (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ)) (j : ℤ) : ℤ) = ((m : ℤ) + (j : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (i : ℤ)) (i : ℤ) : ℤ) := by parley_subst_at s7 s6
  all_goals exact s8

end Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep
