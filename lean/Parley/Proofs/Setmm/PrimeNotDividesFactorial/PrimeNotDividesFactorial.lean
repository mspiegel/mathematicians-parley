module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-not-divides-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeNotDividesFactorial.PrimeNotDividesFactorial

theorem prime_not_divides_factorial (P : ℕ) (hH1 : 0 < P) (hH2 : Nat.Prime P) (N : ℕ) (hH4 : (N : ℤ) < (P : ℤ)) :
    ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ) := by
  -- 1. def:prime p := P, from H2
  have s1 : (P : ℤ) > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. induction on k starting at 1
  have s2 : ∀ k : ℕ, 0 < k → (k : ℤ) < (P : ℤ) → ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      intro hB
      -- 2.1. contradiction
      have s2_1 : ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by
        by_contra hc_hS1
        have hS1 : (P : ℤ) ∣ (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_suppose hc_hS1
        -- 2.1.1. def:factorial
        have s2_1_1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
        -- 2.1.2. substitute 1! = 1 (line 2.1.1) into S1
        have s2_1_2 : (P : ℤ) ∣ (1 : ℤ) := by parley_subst_at s2_1_1 hS1
        -- 2.1.3. mun:divides-one d := P, from 2.1.2
        have s2_1_3 : (P : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_side)
        -- 2.1.4. inequalities
        have s2_1_4 : (P : ℤ) ≠ 1 := by parley_side
        all_goals parley_side
      all_goals parley_side
    | succ k hK hIH =>
      intro hA
      -- 2.2. contradiction
      have s2_2 : ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial ((k : ℤ) + 1) : ℤ) := by
        by_contra hc_hS2
        have hS2 : (P : ℤ) ∣ (LeanBridges.Counting.factorial ((k : ℤ) + 1) : ℤ) := by parley_suppose hc_hS2
        -- 2.2.1. def:factorial n := k
        have s2_2_1 : (LeanBridges.Counting.factorial ((k : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := k))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); parley_side)
        -- 2.2.2. substitute (k + 1)! = k!·(k + 1) (line 2.2.1) into S2
        have s2_2_2 : (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1) := by parley_subst_at s2_2_1 hS2
        -- 2.2.3. thm:prime-divides-product m := k!, n := k + 1, from H2
        have s2_2_3 : (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1) ↔ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1 := by first | exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (n := (k : ℤ) + 1)) | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (n := (k : ℤ) + 1))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (n := (k : ℤ) + 1)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (n := (k : ℤ) + 1)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (n := (k : ℤ) + 1)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (n := (k : ℤ) + 1)); parley_side)
        -- 2.2.4. mun:iff-from-left, from 2.2.2, 2.2.3
        have s2_2_4 : (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1)) (Q := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1)) (Q := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1)) (Q := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1)) (Q := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1)) (Q := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1)) (Q := (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ∨ (P : ℤ) ∣ (k : ℤ) + 1) (by parley_side) (by parley_side)); parley_side)
        -- 2.2.5. inequalities, from A
        have s2_2_5 : (k : ℤ) < (P : ℤ) := by parley_side
        -- 2.2.6. mun:modus-ponens, from IH, 2.2.5
        have s2_2_6 : ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side)); parley_side)
        -- 2.2.7. cases, from 2.2.4
        have s2_2_7 : (P : ℤ) ≤ (k : ℤ) + 1 := by
          rcases s2_2_4 with hC1 | hC2
          · skip
            -- 2.2.7.1. restate 2.2.6
            have s2_2_7_1 : ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) := by parley_side
            all_goals parley_side
          · skip
            -- 2.2.7.2. mun:divides-le e := P, m := k + 1, from C2
            have s2_2_7_2 : (P : ℤ) ≤ (k : ℤ) + 1 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) (by parley_side)); parley_side)
            all_goals parley_side
        -- 2.2.8. inequalities, from 2.2.7
        have s2_2_8 : ¬ (k : ℤ) + 1 < (P : ℤ) := by parley_side
        all_goals parley_side
      all_goals parley_side
  -- 3. axi:excluded-middle P := N = 0
  have s3 : (N : ℤ) = 0 ∨ (N : ℤ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (N : ℤ) = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (N : ℤ) = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (N : ℤ) = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (N : ℤ) = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (N : ℤ) = 0)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (N : ℤ) = 0)); parley_side)
  -- 4. cases, from 3
  have s4 : ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ) := by
    rcases s3 with hC3 | hC4
    · skip
      -- 4.1. arithmetic
      have s4_1 : (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 := by parley_arith
      -- 4.2. substitute N = 0 (C3) into line 4.1
      have s4_2 : (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = 1 := by parley_subst_at hC3 s4_1
      -- 4.3. contradiction
      have s4_3 : ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ) := by
        by_contra hc_hS3
        have hS3 : (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ) := by parley_suppose hc_hS3
        -- 4.3.1. substitute N! = 1 (line 4.2) into S3
        have s4_3_1 : (P : ℤ) ∣ (1 : ℤ) := by parley_subst_at s4_2 hS3
        -- 4.3.2. mun:divides-one d := P, from 4.3.1
        have s4_3_2 : (P : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_side)
        -- 4.3.3. inequalities
        have s4_3_3 : (P : ℤ) ≠ 1 := by parley_side
        all_goals parley_side
      all_goals parley_side
    · skip
      -- 4.4. mun:nat0-nonzero m := N, from C4
      have s4_4 : 0 < N := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side)); parley_side)
      -- 4.5. instantiate k := N in line 2, from 4.4
      have s4_5 : (N : ℤ) < (P : ℤ) → ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ) := by first | exact (s2 N (by parley_side)) | exact ((s2 N (by parley_side))).symm | simpa using (s2 N (by parley_side)) | exact_mod_cast (s2 N (by parley_side)) | (have h := (s2 N (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (s2 N (by parley_side)); parley_side)
      -- 4.6. mun:modus-ponens, from H4, 4.5
      have s4_6 : ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (N : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (N : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (N : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (N : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (N : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (N : ℤ) < (P : ℤ)) (Q := ¬ (P : ℤ) ∣ (LeanBridges.Counting.factorial (N : ℤ) : ℤ)) (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.PrimeNotDividesFactorial.PrimeNotDividesFactorial
