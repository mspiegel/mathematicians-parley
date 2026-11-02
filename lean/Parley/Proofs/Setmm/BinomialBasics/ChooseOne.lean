module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseOne

theorem choose_one (N : ℕ) :
    (LeanBridges.Counting.choose (N : ℤ) (1 : ℤ) : ℤ) = (N : ℤ) := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ (N : ℤ) = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side); parley_side)
  -- 2. cases, from 1
  have s2 : (LeanBridges.Counting.choose (N : ℤ) (1 : ℤ) : ℤ) = (N : ℤ) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:nat-minus-one n := N, from C1
      have s2_1 : 0 ≤ (N : ℤ) - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)); parley_side)
      -- 2.2. inequalities, from C1
      have s2_2a : (0 : ℤ) ≤ 1 := by parley_side
      have s2_2b : 1 ≤ (N : ℤ) := by parley_side
      -- 2.3. def:range-between k := 1, a := 0, b := N, from 2.2
      have s2_3 : (1 : ℤ) ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (1 : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (1 : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side); parley_side)
      -- 2.4. def:factorial
      have s2_4 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
      -- 2.5. thm:factorial-by-predecessor, from C1
      have s2_5 : (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side))).symm | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side)); parley_side)
      -- 2.6. mun:factorial-nat n := N − 1, from 2.1
      have s2_6 : 0 < (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := ((N : ℤ) - 1).toNat))); parley_side)
      -- 2.7. calculation
      have s2_7 : (LeanBridges.Counting.choose (N : ℤ) (1 : ℤ) : ℤ) = (N : ℤ) := by
        qify
        calc (LeanBridges.Counting.choose (N : ℤ) (1 : ℤ) : ℚ) = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ) * (LeanBridges.Counting.factorial (1 : ℤ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (1 : ℤ))) (by parley_side); parley_side)
          _ = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ) * 1) := by
              have s2_4_w : (LeanBridges.Counting.factorial (1 : ℤ) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_4_w | parley_subst s2_4
          _ = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ) * (N : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ) * 1) := by
              have s2_5_w : (LeanBridges.Counting.factorial (N : ℤ) : ℚ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℚ) * (N : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_5_w | parley_subst s2_5
          _ = (N : ℚ) := by parley_ring
      all_goals parley_side
    · skip
      -- 2.8. arithmetic
      have s2_8 : (0 : ℤ) < 1 := by parley_arith
      -- 2.9. substitute N = 0 (C2) into line 2.8
      have s2_9 : (N : ℤ) < 1 := by parley_subst_at hC2 s2_8
      -- 2.10. calculation
      have s2_10 : (LeanBridges.Counting.choose (N : ℤ) (1 : ℤ) : ℤ) = (N : ℤ) := by
        calc (LeanBridges.Counting.choose (N : ℤ) (1 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (k := (1 : ℤ))) (by parley_side); parley_side)
          _ = (N : ℤ) := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.BinomialBasics.ChooseOne
