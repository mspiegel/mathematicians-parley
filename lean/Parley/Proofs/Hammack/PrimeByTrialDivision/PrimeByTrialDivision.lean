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
theorem prime_by_trial_division (p : ℕ) (hH1 : 0 < p) (hH2 : (p : ℤ) > 1) (hH3 : ∀ n : ℕ, 0 < n → 2 ≤ (n : ℤ) ∧ (n : ℝ) ≤ Real.sqrt (p : ℝ) → ¬ (n : ℤ) ∣ (p : ℤ)) :
    Nat.Prime p := by
  -- 1. proof
  have s1 : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (p : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (p : ℤ) := by
    intro d hK
    intro hC
    by_contra hc_hS
    have hS : ¬ ((d : ℤ) = 1 ∨ (d : ℤ) = (p : ℤ)) := by parley_suppose hc_hS
    have hD1_kind : ∃ m : ℕ, 0 < m ∧ (m : ℚ) = (p : ℚ) / (d : ℚ) := by first | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := p) (by parley_side) (d := d) (by parley_side))).mp (by parley_side); parley_side)
    obtain ⟨e, hD1_pos, hD1⟩ := hD1_kind
    -- 1.1. algebra, from D1
    have s1_1 : (p : ℤ) = (d : ℤ) * (e : ℤ) := by qify at *; linear_combination (norm := parley_field) (-(d : ℚ)) * hD1
    -- 1.2. mun:not-either P := d = 1, Q := d = p, from S
    have s1_2a : (d : ℤ) ≠ 1 := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).1; parley_side)
    have s1_2b : (d : ℤ) ≠ (p : ℤ) := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (d : ℤ) = 1) (Q := (d : ℤ) = (p : ℤ)))).mp (by parley_side)).2; parley_side)
    -- 1.3. inequalities, from K, 1.2
    have s1_3 : 1 < (d : ℤ) := by parley_order
    -- 1.4. mun:integer-step m := 1, n := d, from 1.3
    have s1_4 : 1 + 1 ≤ (d : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) s1_3)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) s1_3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) s1_3) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (d : ℤ)) s1_3); parley_side)
    -- 1.5. inequalities, from 1.4
    have s1_5 : 2 ≤ (d : ℤ) := by parley_order
    -- 1.6. contradiction
    have s1_6 : (e : ℤ) ≠ 1 := by
      by_contra hc_hS2
      have hS2 : (e : ℤ) = 1 := by parley_suppose hc_hS2
      -- 1.6.1. substitute e = 1 (S2) into line 1.1
      have s1_6_1 : (p : ℤ) = (d : ℤ) := by parley_subst_at hS2 s1_1
      all_goals parley_side
    -- 1.7. inequalities, from D1, 1.6
    have s1_7 : 1 < (e : ℤ) := by parley_order
    -- 1.8. mun:integer-step m := 1, n := e, from 1.7
    have s1_8 : 1 + 1 ≤ (e : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) s1_7)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) s1_7); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) s1_7) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (e : ℤ)) s1_7); parley_side)
    -- 1.9. inequalities, from 1.8
    have s1_9 : 2 ≤ (e : ℤ) := by parley_order
    -- 1.10. mun:nonneg-or-neg x := e − d
    have s1_10 : (e : ℤ) - (d : ℤ) ≥ 0 ∨ (e : ℤ) - (d : ℤ) < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (e : ℤ) - (d : ℤ))) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (e : ℤ) - (d : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (e : ℤ) - (d : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (e : ℤ) - (d : ℤ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (e : ℤ) - (d : ℤ))); parley_side)
    -- 1.11. cases, from 1.10
    have s1_11 : (d : ℤ) = (p : ℤ) := by
      rcases s1_10 with hC1 | hC2
      · skip
        -- 1.11.1. inequalities
        have s1_11_1 : (e : ℤ) ≥ (d : ℤ) := by parley_order
        -- 1.11.2. mun:multiply-le x := d, y := e, c := d, from K, 1.11.1
        have s1_11_2 : (d : ℤ) * (d : ℤ) ≤ (d : ℤ) * (e : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (d : ℤ)) (y := (e : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (d : ℤ)) (y := (e : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (d : ℤ)) (y := (e : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (d : ℤ)) (y := (e : ℤ)) (c := (d : ℤ)) (by parley_side) (by parley_side)); parley_side)
        -- 1.11.3. thm:divisor-exceeds-root, from C, H3, 1.5
        have s1_11_3 : (p : ℤ) < (d : ℤ) * (d : ℤ) := by first | linarith [(Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) (by parley_side) (by parley_side) (by parley_side))] | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) (by parley_side) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := d) (by parley_side) (by parley_side) (by parley_side) (by parley_side)); parley_side)
        -- 1.11.4. transitivity, from 1.11.2, 1.1
        have s1_11_4 : (d : ℤ) * (d : ℤ) ≤ (p : ℤ) := by parley_order
        -- 1.11.5. inequalities, from 1.11.4
        have s1_11_5 : ¬ (p : ℤ) < (d : ℤ) * (d : ℤ) := by parley_side
        all_goals parley_side
      · skip
        -- 1.11.6. inequalities
        have s1_11_6 : (e : ℤ) ≤ (d : ℤ) := by parley_order
        -- 1.11.7. mun:multiply-le x := e, y := d, c := e, from D1, 1.11.6
        have s1_11_7 : (e : ℤ) * (e : ℤ) ≤ (e : ℤ) * (d : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (e : ℚ)) (y := (d : ℚ)) (c := (e : ℚ)) (by parley_side) (by parley_side)); parley_side)
        -- 1.11.8. algebra, from 1.1
        have s1_11_8 : (p : ℤ) = (e : ℤ) * (d : ℤ) := by linear_combination (norm := parley_norm) s1_1
        -- 1.11.9. def:divides d := e, n := p, from 1.11.8
        have s1_11_9 : (e : ℤ) ∣ (p : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (e : ℤ)) (n := (p : ℤ)))).mpr ⟨(d : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (e : ℤ)) (n := (p : ℤ)))).mpr ⟨(d : ℤ), by parley_side⟩; parley_side)
        -- 1.11.10. thm:divisor-exceeds-root d := e, from H3, 1.9, 1.11.9
        have s1_11_10 : (p : ℤ) < (e : ℤ) * (e : ℤ) := by first | linarith [(Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) (by parley_side) (by parley_side) (by parley_side))] | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) (by parley_side) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot.divisor_exceeds_root (p := p) (by parley_side) (d := e) (by parley_side) (by parley_side) (by parley_side) (by parley_side)); parley_side)
        -- 1.11.11. transitivity, from 1.11.7, 1.11.8
        have s1_11_11 : (e : ℤ) * (e : ℤ) ≤ (p : ℤ) := by parley_order
        -- 1.11.12. inequalities, from 1.11.11
        have s1_11_12 : ¬ (p : ℤ) < (e : ℤ) * (e : ℤ) := by parley_side
        all_goals parley_side
    all_goals parley_side
  -- 2. join H2, 1
  have s2a : (p : ℤ) > 1 := by parley_side
  have s2b : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (p : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (p : ℤ) := by intro d h_d; parley_side
  -- 3. def:prime, from 2
  have s3 : Nat.Prime p := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.PrimeByTrialDivision.PrimeByTrialDivision
