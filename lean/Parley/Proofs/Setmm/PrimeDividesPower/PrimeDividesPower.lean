module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-divides-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeDividesPower.PrimeDividesPower

theorem prime_divides_power (P : ℕ) (hH1 : 0 < P) (hH2 : Nat.Prime P) (Q : ℕ) (hH3 : 0 < Q) (hH4 : Nat.Prime Q) (N : ℕ) (hH6 : (P : ℤ) ∣ (Q : ℤ) ^ N) :
    (P : ℤ) = (Q : ℤ) := by
  -- 1. def:prime p := P, from H2
  have s1 : (P : ℤ) > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. def:prime p := Q, from H4
  have s2 : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (Q : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (Q : ℤ) := by first | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := Q) (by parley_side))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Divisibility.def_prime (p := Q) (by parley_side))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Divisibility.def_prime (p := Q) (by parley_side))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := Q) (by parley_side))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := Q) (by parley_side))).mp (by parley_side)).2; parley_side)
  -- 3. induction on m starting at 0
  have s3 : ∀ m : ℕ, (P : ℤ) ∣ (Q : ℤ) ^ m → (P : ℤ) = (Q : ℤ) := by
    intro m
    induction m with
    | zero =>
      intro hC1
      -- 3.1. algebra
      have s3_1 : (Q : ℤ) ^ 0 = 1 := by parley_ring
      -- 3.2. substitute Q^0 = 1 (line 3.1) into C1
      have s3_2 : (P : ℤ) ∣ (1 : ℤ) := by parley_subst_at s3_1 hC1
      -- 3.3. mun:divides-one d := P, from 3.2
      have s3_3 : (P : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_side)
      -- 3.4. inequalities
      have s3_4 : (P : ℤ) ≠ 1 := by parley_side
      all_goals parley_side
    | succ m hIH =>
      intro hC2
      -- 3.5. mun:exponent-step a := Q
      have s3_5 : (Q : ℤ) ^ (m + 1) = (Q : ℤ) ^ m * (Q : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Q : ℤ)) (m := m)); parley_side)
      -- 3.6. substitute Q^(m + 1) = Q^m·Q (line 3.5) into C2
      have s3_6 : (P : ℤ) ∣ (Q : ℤ) ^ m * (Q : ℤ) := by parley_subst_at s3_5 hC2
      -- 3.7. thm:prime-divides-product m := Q^m, n := Q, from H2, 3.6
      have s3_7 : (P : ℤ) ∣ (Q : ℤ) ^ m ∨ (P : ℤ) ∣ (Q : ℤ) := by first | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (Q : ℤ) ^ m) (n := (Q : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (Q : ℤ) ^ m) (n := (Q : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (Q : ℤ) ^ m) (n := (Q : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (Q : ℤ) ^ m) (n := (Q : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) (by parley_side) (m := (Q : ℤ) ^ m) (n := (Q : ℤ)))).mp (by parley_side); parley_side)
      -- 3.8. cases, from 3.7
      have s3_8 : (P : ℤ) = (Q : ℤ) := by
        rcases s3_7 with hC3 | hC4
        · skip
          -- 3.8.1. mun:modus-ponens, from C3, IH
          have s3_8_1 : (P : ℤ) = (Q : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ m) (Q := (P : ℤ) = (Q : ℤ)) hIH hC3); parley_side)
          all_goals parley_side
        · skip
          -- 3.8.2. instantiate d := P in line 2
          have s3_8_2 : (P : ℤ) ∣ (Q : ℤ) → (P : ℤ) = 1 ∨ (P : ℤ) = (Q : ℤ) := by first | exact (s2 P (by parley_side)) | exact ((s2 P (by parley_side))).symm | simpa using (s2 P (by parley_side)) | exact_mod_cast (s2 P (by parley_side)) | (have h := (s2 P (by parley_side)); parley_side)
          -- 3.8.3. mun:modus-ponens, from C4, 3.8.2
          have s3_8_3 : (P : ℤ) = 1 ∨ (P : ℤ) = (Q : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ)) (Q := (P : ℤ) = 1 ∨ (P : ℤ) = (Q : ℤ)) s3_8_2 hC4) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ)) (Q := (P : ℤ) = 1 ∨ (P : ℤ) = (Q : ℤ)) s3_8_2 hC4)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ)) (Q := (P : ℤ) = 1 ∨ (P : ℤ) = (Q : ℤ)) s3_8_2 hC4) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ)) (Q := (P : ℤ) = 1 ∨ (P : ℤ) = (Q : ℤ)) s3_8_2 hC4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ)) (Q := (P : ℤ) = 1 ∨ (P : ℤ) = (Q : ℤ)) s3_8_2 hC4); parley_side)
          -- 3.8.4. cases, from 3.8.3
          have s3_8_4 : (P : ℤ) = (Q : ℤ) := by
            rcases s3_8_3 with hC5 | hC6
            · skip
              -- 3.8.4.1. inequalities
              have s3_8_4_1 : (P : ℤ) ≠ 1 := by parley_side
              all_goals parley_side
            · skip
              all_goals parley_side
          all_goals parley_side
      all_goals parley_side
  -- 4. instantiate m := N in line 3
  have s4 : (P : ℤ) ∣ (Q : ℤ) ^ N → (P : ℤ) = (Q : ℤ) := by first | exact (s3 N) | exact ((s3 N)).symm | simpa using (s3 N) | exact_mod_cast (s3 N) | (have h := (s3 N); parley_side)
  -- 5. mun:modus-ponens, from H6, 4
  have s5 : (P : ℤ) = (Q : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (P : ℤ) ∣ (Q : ℤ) ^ N) (Q := (P : ℤ) = (Q : ℤ)) s4 hH6); parley_side)
  all_goals exact s5

end Parley.Proofs.Setmm.PrimeDividesPower.PrimeDividesPower
