module

public import LeanBridges
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling

/-! Written from proofs/hammack/harmonic-lower-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicLowerBound

theorem harmonic_lower_bound (n : ℕ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ n : ℤ), (1 / (k : ℚ) : ℚ)) ≥ 1 + (n : ℚ) / 2 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on m starting at 1
  have s2 : ∀ m : ℕ, 0 < m → (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ m : ℤ), (1 / (j : ℚ) : ℚ)) ≥ 1 + (m : ℚ) / 2 := by
    intro m h_m
    replace h_m : 1 ≤ m := h_m
    induction m, h_m using Nat.le_induction with
    | base =>
      -- 2.1. mun:sum-single a := 1, from 1
      have s2_1 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (j : ℚ) : ℚ)) = 1 / 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); parley_side)
      -- 2.2. calculation
      have r135_1 : (1 : ℤ) ≥ 1 := by parley_arith
      have s2_2 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ 1 : ℤ), (1 / (j : ℚ) : ℚ)) ≥ 1 + 1 / 2 := by
        calc (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ 1 : ℤ), (1 / (j : ℚ) : ℚ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 + 1 : ℤ), (1 / (j : ℚ) : ℚ)) := by norm_num
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (j : ℚ) : ℚ)) + 1 / (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); parley_side)
          _ = 1 / 1 + 1 / (1 + 1) := by parley_subst s2_1
          _ ≥ 1 + 1 / 2 := by norm_num
      all_goals parley_side
    | succ m hK hIH =>
      -- 2.3. thm:harmonic-doubling j := m
      have s2_3 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ (m + 1) : ℤ), (1 / (j : ℚ) : ℚ)) ≥ (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ m : ℤ), (1 / (j : ℚ) : ℚ)) + 1 / 2 := by first | linarith [(Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling.harmonic_doubling (j := m))] | (have h := (Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling.harmonic_doubling (j := m)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling.harmonic_doubling (j := m)) | (have h := (Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling.harmonic_doubling (j := m)); parley_side)
      -- 2.4. inequalities
      have s2_4 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ m : ℤ), (1 / (j : ℚ) : ℚ)) + 1 / 2 ≥ 1 + ((m : ℚ) + 1) / 2 := by parley_side
      -- 2.5. transitivity, from 2.3, 2.4
      have s2_5 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ (m + 1) : ℤ), (1 / (j : ℚ) : ℚ)) ≥ 1 + ((m : ℚ) + 1) / 2 := by parley_side
      all_goals parley_side
  -- 3. instantiate m := n in line 2
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ n : ℤ), (1 / (k : ℚ) : ℚ)) ≥ 1 + (n : ℚ) / 2 := by first | linarith [(s2 n (by parley_side))] | (have h := (s2 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s2 n (by parley_side)) | (have h := (s2 n (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicLowerBound
