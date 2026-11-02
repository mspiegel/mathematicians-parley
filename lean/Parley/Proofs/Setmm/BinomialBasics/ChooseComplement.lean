module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseComplement

theorem choose_complement (N : ℕ) (K : ℤ) :
    (LeanBridges.Counting.choose (N : ℤ) K : ℤ) = (LeanBridges.Counting.choose (N : ℤ) ((N : ℤ) - K) : ℤ) := by
  -- 1. axi:excluded-middle P := K ∈ {0, …, N}
  have s1 : K ∈ Finset.Icc (0 : ℤ) (N : ℤ) ∨ ¬ K ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := K ∈ Finset.Icc (0 : ℤ) (N : ℤ))) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := K ∈ Finset.Icc (0 : ℤ) (N : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := K ∈ Finset.Icc (0 : ℤ) (N : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := K ∈ Finset.Icc (0 : ℤ) (N : ℤ))) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := K ∈ Finset.Icc (0 : ℤ) (N : ℤ))); parley_side)
  -- 2. cases, from 1
  have s2 : (LeanBridges.Counting.choose (N : ℤ) K : ℤ) = (LeanBridges.Counting.choose (N : ℤ) ((N : ℤ) - K) : ℤ) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:range-nat0 n := N, from C1
      have s2_1 : 0 ≤ K := by first | exact (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := (N : ℤ)) (k := K) (by parley_side)) | exact ((Parley.Items.Stdlib.Sums.mun_range_nat0 (n := (N : ℤ)) (k := K) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := (N : ℤ)) (k := K) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := (N : ℤ)) (k := K) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := (N : ℤ)) (k := K) (by parley_side)); parley_side)
      lift K to ℕ using (id s2_1)
      -- 2.2. mun:range-difference a := 0, n := N, from C1
      have s2_2 : 0 ≤ (N : ℤ) - (K : ℤ) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := (N : ℤ)) (k := (K : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := (N : ℤ)) (k := (K : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := (N : ℤ)) (k := (K : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := (N : ℤ)) (k := (K : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := (N : ℤ)) (k := (K : ℤ)) (by parley_side)); parley_side)
      -- 2.3. inequalities, from 2.1, 2.2
      have s2_3a : 0 ≤ (N : ℤ) - (K : ℤ) := by parley_side
      have s2_3b : (N : ℤ) - (K : ℤ) ≤ (N : ℤ) := by parley_side
      -- 2.4. def:range-between k := N − K, a := 0, b := N, from 2.3
      have s2_4 : (N : ℤ) - (K : ℤ) ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - (K : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - (K : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side); parley_side)
      -- 2.5. algebra
      have s2_5 : (N : ℤ) - ((N : ℤ) - (K : ℤ)) = (K : ℤ) := by parley_ring
      -- 2.6. substitute N − (N − K) = K (line 2.5)
      have s2_6 : (LeanBridges.Counting.factorial ((N : ℤ) - ((N : ℤ) - (K : ℤ))) : ℤ) = (LeanBridges.Counting.factorial (K : ℤ) : ℤ) := by parley_subst s2_5
      -- 2.7. mun:factorial-nat n := N − K, from 2.2
      have s2_7 : 0 < (LeanBridges.Counting.factorial ((N : ℤ) - (K : ℤ)) : ℤ) := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - (K : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - (K : ℤ)).toNat))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - (K : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - (K : ℤ)).toNat)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - (K : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - (K : ℤ)).toNat))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - (K : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - (K : ℤ)).toNat))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - (K : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - (K : ℤ)).toNat))); parley_side)
      -- 2.8. mun:factorial-nat n := K, from 2.1
      have s2_8 : 0 < (LeanBridges.Counting.factorial (K : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := K)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := K))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := K)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := K)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := K)); parley_side)
      -- 2.9. calculation
      have s2_9 : (LeanBridges.Counting.choose (N : ℤ) (K : ℤ) : ℤ) = (LeanBridges.Counting.choose (N : ℤ) ((N : ℤ) - (K : ℤ)) : ℤ) := by
        qify
        calc (LeanBridges.Counting.choose (N : ℤ) (K : ℤ) : ℚ) = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) - (K : ℤ)) : ℚ) * (LeanBridges.Counting.factorial (K : ℤ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (K : ℤ))) (by parley_side); parley_side)
          _ = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) / ((LeanBridges.Counting.factorial (K : ℤ) : ℚ) * (LeanBridges.Counting.factorial ((N : ℤ) - (K : ℤ)) : ℚ)) := by parley_ring
          _ = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) - ((N : ℤ) - (K : ℤ))) : ℚ) * (LeanBridges.Counting.factorial ((N : ℤ) - (K : ℤ)) : ℚ)) := by
              have s2_6_w : (LeanBridges.Counting.factorial ((N : ℤ) - ((N : ℤ) - (K : ℤ))) : ℚ) = (LeanBridges.Counting.factorial (K : ℤ) : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_6; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_6_w | parley_subst s2_6
          _ = (LeanBridges.Counting.choose (N : ℤ) ((N : ℤ) - (K : ℤ)) : ℚ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ) - (K : ℤ))) (by parley_side); parley_side)
      all_goals parley_side
    · skip
      -- 2.10. contradiction
      have s2_10 : ¬ (N : ℤ) - K ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by
        by_contra hc_hS
        have hS : (N : ℤ) - K ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by parley_suppose hc_hS
        -- 2.10.1. def:range-between k := N − K, a := 0, b := N, from S
        have s2_10_1a : 0 ≤ (N : ℤ) - K := by first | linarith [(((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).1] | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).1; parley_side)
        have s2_10_1b : (N : ℤ) - K ≤ (N : ℤ) := by first | linarith [(((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).2] | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - K) (a := (0 : ℤ)) (b := (N : ℤ)))).mp (by parley_side)).2; parley_side)
        -- 2.10.2. inequalities
        have s2_10_2 : K ≥ 0 := by parley_side
        -- 2.10.3. inequalities
        have s2_10_3 : K ≤ (N : ℤ) := by parley_side
        -- 2.10.4. def:range-between k := K, a := 0, b := N, from 2.10.2, 2.10.3
        have s2_10_4 : K ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := K) (a := (0 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := K) (a := (0 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side); parley_side)
        -- 2.10.5. restate C2
        have s2_10_5 : ¬ K ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by parley_side
        all_goals parley_side
      -- 2.11. calculation
      have s2_11 : (LeanBridges.Counting.choose (N : ℤ) K : ℤ) = (LeanBridges.Counting.choose (N : ℤ) ((N : ℤ) - K) : ℤ) := by
        calc (LeanBridges.Counting.choose (N : ℤ) K : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := K) (by parley_side)); parley_side)
          _ = (LeanBridges.Counting.choose (N : ℤ) ((N : ℤ) - K) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (k := (N : ℤ) - K) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.BinomialBasics.ChooseComplement
