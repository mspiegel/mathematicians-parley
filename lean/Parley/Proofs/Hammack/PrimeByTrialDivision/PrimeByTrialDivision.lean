module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot

/-! Written from proofs/hammack/prime-by-trial-division.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeByTrialDivision.PrimeByTrialDivision

set_option maxHeartbeats 600000 in
theorem prime_by_trial_division (p : ℤ) (hH1 : 0 < p) (hH2 : p > 1) (hH3 : ∀ n : ℤ, 0 < n → 2 ≤ n ∧ (n : ℝ) ≤ Real.sqrt (p : ℝ) → ¬ n ∣ p) :
    Nat.Prime p.toNat := by
  -- 1. proof
  have s1 : ∀ d : ℤ, 0 < d → d ∣ p → d = 1 ∨ d = p := by
    intro d hK
    intro hC
    by_contra hc_hS
    have hS : ¬ (d = 1 ∨ d = p) := by parley_suppose hc_hS
    have hD1_kind : ∃ m : ℤ, 0 < m ∧ (m : ℚ) = (p : ℚ) / (d : ℚ) := by first | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side); parley_side)
    obtain ⟨e, hD1_pos, hD1⟩ := hD1_kind
    -- 1.1. algebra, from D1
    have s1_1 : p = d * e := by qify at *; linear_combination (norm := parley_field) (-(d : ℚ)) * hD1
    -- 1.2. mun:not-either P := d = 1, Q := d = p, from S
    have s1_2a : d ≠ 1 := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).1; parley_side)
    have s1_2b : d ≠ p := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := d = 1) (Q := d = p))).mp (by parley_side)).2; parley_side)
    -- 1.3. inequalities, from K, 1.2
    have s1_3 : 1 < d := by parley_order
    -- 1.4. mun:integer-step m := 1, n := d, from 1.3
    have s1_4 : 1 + 1 ≤ d := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) s1_3)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) s1_3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) s1_3) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) s1_3); parley_side)
    -- 1.5. inequalities, from 1.4
    have s1_5 : 2 ≤ d := by parley_order
    -- 1.6. contradiction
    have s1_6 : e ≠ 1 := by
      by_contra hc_hS2
      have hS2 : e = 1 := by parley_suppose hc_hS2
      -- 1.6.1. substitute e = 1 (S2) into line 1.1
      have s1_6_1 : p = d := by parley_subst_at hS2 s1_1
      all_goals parley_side
    -- 1.7. inequalities, from D1, 1.6
    have s1_7 : 1 < e := by parley_order
    -- 1.8. mun:integer-step m := 1, n := e, from 1.7
    have s1_8 : 1 + 1 ≤ e := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := e) s1_7)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := e) s1_7); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := e) s1_7) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := e) s1_7); parley_side)
    -- 1.9. inequalities, from 1.8
    have s1_9 : 2 ≤ e := by parley_order
    -- 1.10. mun:nonneg-or-neg x := e − d
    have s1_10 : e - d ≥ 0 ∨ e - d < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := e - d)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := e - d))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := e - d)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := e - d)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := e - d)); parley_side)
    -- 1.11. cases, from 1.10
    have s1_11 : d = p := by
      rcases s1_10 with hC1 | hC2
      · skip
        -- 1.11.1. inequalities
        have s1_11_1 : e ≥ d := by parley_order
        -- 1.11.2. mun:multiply-le x := d, y := e, c := d, from K, 1.11.1
        have s1_11_2 : d * d ≤ d * e := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := d) (y := e) (c := d) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := d) (y := e) (c := d) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := d) (y := e) (c := d) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := d) (y := e) (c := d) (by parley_side) (by parley_side)); parley_side)
        -- 1.11.3. thm:divisor-exceeds-root, from C, H3, 1.5
        have s1_11_3 : p < d * d := by first | linarith [(Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) s1_5 hC hH3)] | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) s1_5 hC hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) s1_5 hC hH3) | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) s1_5 hC hH3); parley_side)
        -- 1.11.4. transitivity, from 1.11.2, 1.1
        have s1_11_4 : d * d ≤ p := by parley_order
        -- 1.11.5. inequalities, from 1.11.4
        have s1_11_5 : ¬ p < d * d := by parley_side
        all_goals parley_side
      · skip
        -- 1.11.6. inequalities
        have s1_11_6 : e ≤ d := by parley_order
        -- 1.11.7. mun:multiply-le x := e, y := d, c := e, from D1, 1.11.6
        have s1_11_7 : e * e ≤ e * d := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side)); parley_side)
        -- 1.11.8. algebra, from 1.1
        have s1_11_8 : p = e * d := by linear_combination (norm := parley_norm) s1_1
        -- 1.11.9. def:divides d := e, n := p, from 1.11.8
        have s1_11_9 : e ∣ p := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := e) (n := p))).mpr ⟨d, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := e) (n := p))).mpr ⟨d, by parley_side⟩; parley_side)
        -- 1.11.10. thm:divisor-exceeds-root d := e, from H3, 1.9, 1.11.9
        have s1_11_10 : p < e * e := by first | linarith [(Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) s1_9 s1_11_9 hH3)] | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) s1_9 s1_11_9 hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) s1_9 s1_11_9 hH3) | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) s1_9 s1_11_9 hH3); parley_side)
        -- 1.11.11. transitivity, from 1.11.7, 1.11.8
        have s1_11_11 : e * e ≤ p := by parley_order
        -- 1.11.12. inequalities, from 1.11.11
        have s1_11_12 : ¬ p < e * e := by parley_side
        all_goals parley_side
    all_goals parley_side
  -- 2. join H2, 1
  have s2a : p > 1 := by parley_side
  have s2b : ∀ d : ℤ, 0 < d → d ∣ p → d = 1 ∨ d = p := by intro d h_d; parley_side
  -- 3. def:prime, from 2
  have s3 : Nat.Prime p.toNat := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.PrimeByTrialDivision.PrimeByTrialDivision
