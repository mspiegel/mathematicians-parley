module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/lcm-equals-first.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LcmEqualsFirst.LcmEqualsFirst

theorem lcm_equals_first (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) :
    ((a : ℤ) = (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ↔ (b : ℤ) ∣ (a : ℤ)) := by
  -- 1. def:lcm
  have s1 : (b : ℤ) ∣ (Int.lcm (a : ℤ) (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_lcm_3 (a := (a : ℤ)) (b := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.def_lcm_3 (a := (a : ℤ)) (b := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_lcm_3 (a := (a : ℤ)) (b := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_lcm_3 (a := (a : ℤ)) (b := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.def_lcm_3 (a := (a : ℤ)) (b := (b : ℤ))); parley_side)
  -- 2. def:lcm
  have s2 : (a : ℤ) ∣ (Int.lcm (a : ℤ) (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := (a : ℤ)) (b := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := (a : ℤ)) (b := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := (a : ℤ)) (b := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := (a : ℤ)) (b := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := (a : ℤ)) (b := (b : ℤ))); parley_side)
  -- 3. def:lcm
  have s3 : 0 ≤ (Int.lcm (a : ℤ) (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_lcm_1 (a := (a : ℤ)) (b := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.def_lcm_1 (a := (a : ℤ)) (b := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_lcm_1 (a := (a : ℤ)) (b := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_lcm_1 (a := (a : ℤ)) (b := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.def_lcm_1 (a := (a : ℤ)) (b := (b : ℤ))); parley_side)
  -- 4. def:lcm
  have s4 : ∀ k : ℤ, (a : ℤ) ∣ k ∧ (b : ℤ) ∣ k → (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ k := by first | exact (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := (a : ℤ)) (b := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := (a : ℤ)) (b := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := (a : ℤ)) (b := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := (a : ℤ)) (b := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := (a : ℤ)) (b := (b : ℤ))); parley_side)
  -- 5. both directions
  have s5 : (a : ℤ) = (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ↔ (b : ℤ) ∣ (a : ℤ) := by
    constructor
    · skip
      intro hD1
      -- 5.1. substitute a = lcm(a, b) (D1) into line 1
      have s5_1 : (b : ℤ) ∣ (a : ℤ) := by parley_subst_at hD1 s1
      all_goals parley_side
    · skip
      intro hD2
      -- 5.2. mun:divides-self n := a
      have s5_2 : (a : ℤ) ∣ (a : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (a : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (a : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (a : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (a : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (a : ℤ))); parley_side)
      -- 5.3. join 5.2, D2
      have s5_3a : (a : ℤ) ∣ (a : ℤ) := by parley_side
      have s5_3b : (b : ℤ) ∣ (a : ℤ) := by parley_side
      -- 5.4. instantiate k := a in line 4
      have s5_4 : (a : ℤ) ∣ (a : ℤ) ∧ (b : ℤ) ∣ (a : ℤ) → (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ) := by first | exact (s4 (a : ℤ)) | exact ((s4 (a : ℤ))).symm | simpa using (s4 (a : ℤ)) | exact_mod_cast (s4 (a : ℤ)) | (have h := (s4 (a : ℤ)); parley_side)
      -- 5.5. mun:modus-ponens P := a divides a and b divides a, from 5.3, 5.4
      have s5_5 : (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (a : ℤ) ∣ (a : ℤ) ∧ (b : ℤ) ∣ (a : ℤ)) (Q := (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ)) s5_4 (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (a : ℤ) ∣ (a : ℤ) ∧ (b : ℤ) ∣ (a : ℤ)) (Q := (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ)) s5_4 (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (a : ℤ) ∣ (a : ℤ) ∧ (b : ℤ) ∣ (a : ℤ)) (Q := (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ)) s5_4 (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (a : ℤ) ∣ (a : ℤ) ∧ (b : ℤ) ∣ (a : ℤ)) (Q := (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ)) s5_4 (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (a : ℤ) ∣ (a : ℤ) ∧ (b : ℤ) ∣ (a : ℤ)) (Q := (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ∣ (a : ℤ)) s5_4 (by parley_side)); parley_side)
      -- 5.6. contradiction
      have s5_6 : (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ≠ 0 := by
        by_contra hc_hS
        have hS : (Int.lcm (a : ℤ) (b : ℤ) : ℤ) = 0 := by parley_suppose hc_hS
        -- 5.6.1. substitute lcm(a, b) = 0 (S) into line 5.5
        have s5_6_1 : (0 : ℤ) ∣ (a : ℤ) := by parley_subst_at hS s5_5
        -- 5.6.2. mun:zero-divides n := a, from 5.6.1
        have s5_6_2 : (a : ℤ) = 0 := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side) | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side)).symm | (have h := ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (a : ℤ)))).mp (by parley_side); parley_side)
        -- 5.6.3. inequalities, from H1
        have s5_6_3 : (a : ℤ) ≠ 0 := by parley_side
        all_goals parley_side
      -- 5.7. inequalities, from 3, 5.6
      have s5_7 : 0 < (Int.lcm (a : ℤ) (b : ℤ) : ℤ) := by parley_order
      -- 5.8. mun:pos-int-nat m := lcm(a, b), from 5.7
      have s5_8 : 0 < (Int.lcm (a : ℤ) (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (Int.lcm (a : ℤ) (b : ℤ) : ℤ)) s5_7) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (Int.lcm (a : ℤ) (b : ℤ) : ℤ)) s5_7)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (Int.lcm (a : ℤ) (b : ℤ) : ℤ)) s5_7) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (Int.lcm (a : ℤ) (b : ℤ) : ℤ)) s5_7) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (Int.lcm (a : ℤ) (b : ℤ) : ℤ)) s5_7); parley_side)
      -- 5.9. mun:divides-le e := lcm(a, b), m := a, from 5.5, 5.8
      have s5_9 : (Int.lcm (a : ℤ) (b : ℤ) : ℤ) ≤ (a : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (m := a) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (m := a) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (m := a) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (m := a) (by parley_side) (by parley_side)); parley_side)
      -- 5.10. mun:divides-le e := a, m := lcm(a, b), from 2, 5.8
      have s5_10 : (a : ℤ) ≤ (Int.lcm (a : ℤ) (b : ℤ) : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := a) (by parley_side) (m := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := a) (by parley_side) (m := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := a) (by parley_side) (m := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := a) (by parley_side) (m := Int.lcm (a : ℤ) (b : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 5.11. antisymmetry, from 5.9, 5.10
      have s5_11 : (a : ℤ) = (Int.lcm (a : ℤ) (b : ℤ) : ℤ) := by parley_side
      all_goals parley_side
  all_goals exact s5

end Parley.Proofs.Hammack.LcmEqualsFirst.LcmEqualsFirst
