module

public import AlgebraTactics
public import Counting
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor

/-! Written from proofs/setmm/choose-two-less.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoLess.ChooseTwoLess

theorem choose_two_less (N : ℕ) :
    (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ (N : ℤ) = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side); parley_side)
  -- 2. cases, from 1
  have s2 : (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:nat-minus-one n := N, from C1
      have s2_1 : 0 ≤ (N : ℤ) - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)); parley_side)
      -- 2.2. def:nat0 n := N − 1, from 2.1
      have s2_2 : 0 < (N : ℤ) - 1 ∨ (N : ℤ) - 1 = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side); parley_side)
      -- 2.3. cases, from 2.2
      have s2_3 : (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
        rcases s2_2 with hC3 | hC4
        · skip
          -- 2.3.1. mun:factorial-nat n := N − 1, from C3
          have s2_3_1 : 0 < (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))); parley_side)
          -- 2.3.2. inequalities, from C1
          have s2_3_2a : 0 ≤ (N : ℤ) - 1 := by parley_order
          have s2_3_2b : (N : ℤ) - 1 ≤ (N : ℤ) + 1 := by parley_order
          -- 2.3.3. def:range-between k := N − 1, a := 0, b := N + 1, from 2.3.2
          have s2_3_3 : (N : ℤ) - 1 ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - 1) (a := (0 : ℤ)) (b := (N : ℤ) + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ) - 1) (a := (0 : ℤ)) (b := (N : ℤ) + 1))).mpr (by parley_side); parley_side)
          -- 2.3.4. algebra
          have s2_3_4 : (N : ℤ) + 1 - ((N : ℤ) - 1) = 2 := by parley_ring
          -- 2.3.5. def:factorial n := 1
          have s2_3_5 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); parley_side)
          -- 2.3.6. substitute 1 + 1 = 2 (arithmetic) into line 2.3.5
          have s2_3_6 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * 2 := by parley_subst_at (show (1 + 1 : ℤ) = 2 by parley_side) s2_3_5
          -- 2.3.7. substitute
          have s2_3_7 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by
            have c1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
            have row1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_subst_at c1 s2_3_6
            exact row1
          -- 2.3.8. calculation
          have s2_3_8 : (LeanBridges.Counting.factorial ((N : ℤ) + 1 - ((N : ℤ) - 1)) : ℤ) = 2 := by
            calc (LeanBridges.Counting.factorial ((N : ℤ) + 1 - ((N : ℤ) - 1)) : ℤ) = (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) := by parley_subst s2_3_4
              _ = 1 * 2 := by parley_side
              _ = 2 := by norm_num
          -- 2.3.9. thm:factorial-by-predecessor, from C1
          have s2_3_9 : (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side))).symm | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); parley_side)
          -- 2.3.10. calculation
          have s2_3_10 : (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) * ((N : ℤ) + 1) := by
            calc (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (N : ℤ) : ℤ) * ((N : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := N))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); parley_side)
              _ = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) * ((N : ℤ) + 1) := by parley_subst s2_3_9
          -- 2.3.11. calculation
          have s2_3_11 : (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
            calc (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) + 1 - ((N : ℤ) - 1)) : ℚ) * (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ) - 1)) (by parley_side); parley_side)
              _ = (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) / (2 * (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ)) := by
                  have s2_3_8_w : (LeanBridges.Counting.factorial ((N : ℤ) + 1 - ((N : ℤ) - 1)) : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_3_8; push_cast at h; linear_combination (norm := parley_norm) h
                  first | parley_subst s2_3_8_w | parley_subst s2_3_8
              _ = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ) * (N : ℚ) * ((N : ℚ) + 1) / (2 * (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ)) := by
                  have s2_3_10_w : (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ) * (N : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_3_10; push_cast at h; linear_combination (norm := parley_norm) h
                  first | parley_subst s2_3_10_w | parley_subst s2_3_10
              _ = ((N : ℚ) + 1) * (N : ℚ) / 2 := by parley_ring
          all_goals parley_side
        · skip
          -- 2.3.12. calculation
          have s2_3_12 : (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
            calc (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = (LeanBridges.Counting.choose ((N : ℤ) + 1) (0 : ℤ) : ℚ) := by
                  have hC4_w : (N : ℚ) - 1 = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hC4; push_cast at h; linear_combination (norm := parley_norm) h
                  first | parley_subst hC4_w | parley_subst hC4
              _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1)); parley_side)
              _ = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
                  have hC4_w : (N : ℚ) - 1 = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hC4; push_cast at h; linear_combination (norm := parley_norm) h
                  linear_combination (norm := parley_norm) ((-(N : ℚ) - 2) / ((2))) * hC4_w
          all_goals parley_side
      all_goals parley_side
    · skip
      -- 2.4. algebra, from C2
      have s2_4 : (N : ℤ) + 1 = 1 := by linear_combination (norm := parley_norm) hC2
      -- 2.5. algebra, from C2
      have s2_5 : (N : ℤ) - 1 = -1 := by linear_combination (norm := parley_norm) hC2
      -- 2.6. calculation
      have s2_6 : (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
        calc (LeanBridges.Counting.choose ((N : ℤ) + 1) ((N : ℤ) - 1) : ℚ) = (LeanBridges.Counting.choose (1 : ℤ) ((N : ℤ) - 1) : ℚ) := by
              have s2_4_w : (N : ℚ) + 1 = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_4_w | parley_subst s2_4
          _ = (LeanBridges.Counting.choose (1 : ℤ) (-1 : ℤ) : ℚ) := by
              have s2_5_w : (N : ℚ) - 1 = -1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_5_w | parley_subst s2_5
          _ = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)) | (have h := (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_1 (n := 1))).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_1 (n := 1)); parley_side)
          _ = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
              have hC2_w : (N : ℚ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hC2; push_cast at h; linear_combination (norm := parley_norm) h
              linear_combination (norm := parley_norm) ((-(N : ℚ) - 1) / ((2))) * hC2_w
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.ChooseTwoLess.ChooseTwoLess
