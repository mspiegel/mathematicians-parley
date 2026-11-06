module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-not-divides-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeNotDividesFactorial.PrimeNotDividesFactorial

set_option maxHeartbeats 600000 in
theorem prime_not_divides_factorial (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) (N : ℤ) (hH3 : 0 ≤ N) (hH4 : N < P) :
    ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ) := by
  -- 1. def:prime p := P, from H2
  have s1 : P > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. induction on k starting at 1
  have s2 : ∀ k : ℤ, 0 < k → k < P → ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      intro hB
      -- 2.1. contradiction
      have s2_1 : ¬ P ∣ (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by
        by_contra hc_hS1
        have hS1 : P ∣ (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_suppose hc_hS1
        -- 2.1.1. def:factorial
        have s2_1_1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
        -- 2.1.2. substitute 1! = 1 (line 2.1.1) into S1
        have s2_1_2 : P ∣ (1 : ℤ) := by first | parley_subst_at s2_1_1 hS1 | (have e_nat : LeanBridges.Counting.factorial (1 : ℤ) = 1 := by exact_mod_cast s2_1_1; parley_subst_at e_nat hS1)
        -- 2.1.3. mun:divides-one d := P, from 2.1.2
        have s2_1_3 : P = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_1_2); parley_side)
        -- 2.1.4. inequalities
        have s2_1_4 : P ≠ 1 := by parley_side
        all_goals parley_side
      all_goals parley_side
    | succ k hK hIH =>
      intro hA
      -- 2.2. contradiction
      have s2_2 : ¬ P ∣ (LeanBridges.Counting.factorial (k + 1) : ℤ) := by
        by_contra hc_hS2
        have hS2 : P ∣ (LeanBridges.Counting.factorial (k + 1) : ℤ) := by parley_suppose hc_hS2
        -- 2.2.1. def:factorial n := k
        have s2_2_1 : (LeanBridges.Counting.factorial (k + 1) : ℤ) = (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); parley_side)
        -- 2.2.2. substitute (k + 1)! = k!·(k + 1) (line 2.2.1) into S2
        have s2_2_2 : P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by parley_subst_at s2_2_1 hS2
        -- 2.2.3. thm:prime-divides-product m := k!, n := k + 1, from H2
        have s2_2_3 : P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1) ↔ P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1 := by first | exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) hH2 (m := (LeanBridges.Counting.factorial k : ℤ)) (n := k + 1)) | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) hH2 (m := (LeanBridges.Counting.factorial k : ℤ)) (n := k + 1))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) hH2 (m := (LeanBridges.Counting.factorial k : ℤ)) (n := k + 1)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) hH2 (m := (LeanBridges.Counting.factorial k : ℤ)) (n := k + 1)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) hH2 (m := (LeanBridges.Counting.factorial k : ℤ)) (n := k + 1)); parley_side)
        -- 2.2.4. mun:iff-from-left, from 2.2.2, 2.2.3
        have s2_2_4 : P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1)) (Q := P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1) s2_2_3 s2_2_2) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1)) (Q := P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1) s2_2_3 s2_2_2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1)) (Q := P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1) s2_2_3 s2_2_2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1)) (Q := P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1) s2_2_3 s2_2_2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1)) (Q := P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1) s2_2_3 s2_2_2); parley_side)
        -- 2.2.5. inequalities, from A
        have s2_2_5 : k < P := by parley_order
        -- 2.2.6. mun:modus-ponens, from IH, 2.2.5
        have s2_2_6 : ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := k < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ)) hIH s2_2_5) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := k < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ)) hIH s2_2_5)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := k < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ)) hIH s2_2_5) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := k < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ)) hIH s2_2_5) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := k < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ)) hIH s2_2_5); parley_side)
        -- 2.2.7. cases, from 2.2.4
        have s2_2_7 : P ≤ k + 1 := by
          rcases s2_2_4 with hC1 | hC2
          · skip
            -- 2.2.7.1. restate 2.2.6
            have s2_2_7_1 : ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ) := by parley_side
            all_goals parley_side
          · skip
            -- 2.2.7.2. mun:divides-le e := P, m := k + 1, from C2
            have s2_2_7_2 : P ≤ k + 1 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) hC2)] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) hC2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) hC2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) (by parley_side) (m := k + 1) (by parley_side) hC2); parley_side)
            all_goals parley_side
        -- 2.2.8. inequalities, from 2.2.7
        have s2_2_8 : ¬ k + 1 < P := by parley_side
        all_goals parley_side
      all_goals parley_side
  -- 3. axi:excluded-middle P := N = 0
  have s3 : N = 0 ∨ N ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := N = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := N = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := N = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := N = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := N = 0)); parley_side)
  -- 4. cases, from 3
  have s4 : ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ) := by
    rcases s3 with hC3 | hC4
    · skip
      -- 4.1. arithmetic
      have s4_1 : (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 := by parley_arith
      -- 4.2. substitute N = 0 (C3) into line 4.1
      have s4_2 : (LeanBridges.Counting.factorial N : ℤ) = 1 := by parley_subst_at hC3 s4_1
      -- 4.3. contradiction
      have s4_3 : ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ) := by
        by_contra hc_hS3
        have hS3 : P ∣ (LeanBridges.Counting.factorial N : ℤ) := by parley_suppose hc_hS3
        -- 4.3.1. substitute N! = 1 (line 4.2) into S3
        have s4_3_1 : P ∣ (1 : ℤ) := by first | parley_subst_at s4_2 hS3 | (have e_nat : LeanBridges.Counting.factorial N = 1 := by exact_mod_cast s4_2; parley_subst_at e_nat hS3)
        -- 4.3.2. mun:divides-one d := P, from 4.3.1
        have s4_3_2 : P = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s4_3_1); parley_side)
        -- 4.3.3. inequalities
        have s4_3_3 : P ≠ 1 := by parley_side
        all_goals parley_side
      all_goals parley_side
    · skip
      -- 4.4. mun:nat0-nonzero m := N, from C4
      have s4_4 : 0 < N := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side) hC4) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side) hC4)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side) hC4) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side) hC4) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) (by parley_side) hC4); parley_side)
      -- 4.5. instantiate k := N in line 2, from 4.4
      have s4_5 : N < P → ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ) := by first | exact (s2 N (by parley_side)) | exact ((s2 N (by parley_side))).symm | simpa using (s2 N (by parley_side)) | exact_mod_cast (s2 N (by parley_side)) | (have h := (s2 N (by parley_side)); parley_side)
      -- 4.6. mun:modus-ponens, from H4, 4.5
      have s4_6 : ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := N < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ)) s4_5 hH4) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := N < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ)) s4_5 hH4)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := N < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ)) s4_5 hH4) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := N < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ)) s4_5 hH4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := N < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ)) s4_5 hH4); parley_side)
      all_goals parley_side
  all_goals exact s4

end Parley.Proofs.Setmm.PrimeNotDividesFactorial.PrimeNotDividesFactorial
