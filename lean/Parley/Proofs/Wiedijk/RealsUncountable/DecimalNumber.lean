module

public import AlgebraTactics
public import Divisibility
public import Functions
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.DecimalNumber

set_option maxHeartbeats 2600000 in
theorem decimal_number (d : ℤ → ℤ) (hH2 : ∀ n : ℕ, 0 < n → 0 ≤ (d (n : ℤ) : ℝ) ∧ (d (n : ℤ) : ℝ) ≤ 9) :
    (∃ x : ℝ, ∀ n : ℕ, 0 < n → ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ) ∨ ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) := by
  obtain ⟨N, hD3⟩ : ∃ N : ℤ → ℤ, N 0 = (0 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → N (k + 1) = 10 * N k + d (k + 1) := LeanBridges.Functions.recursion_exists _ (fun k v => 10 * v + d (k + 1))
  set S : Set ℝ := {y : ℝ | ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k} with hD4
  set L : ℤ → ℝ := fun k => (N k : ℝ) / 10 ^ k with hD5
  set U : ℤ → ℝ := fun k => ((N k : ℝ) + 1) / 10 ^ k with hD6
  -- 1. D3
  have s1 : (N 0 : ℝ) = 0 := by have h := hD3.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
  -- 2. induction on k starting at 0
  -- what this block shows, Lean's types give
  -- 3. proof
  have s3 : ∀ k : ℕ, L (k : ℤ) ≤ L ((k : ℤ) + 1) ∧ U ((k : ℤ) + 1) ≤ U (k : ℤ) := by
    intro k
    -- 3.1. D3
    have s3_1 : (N ((k : ℤ) + 1) : ℝ) = 10 * (N (k : ℤ) : ℝ) + (d ((k : ℤ) + 1) : ℝ) := by have h := (hD3.2 (((k : ℤ) + 1) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
    -- 3.2. mun:pos-int-nat
    have r192_1 : 0 < (k : ℝ) + 1 := by parley_order
    have s3_2 : 0 < (k : ℤ) + 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (k : ℤ) + 1) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (k : ℤ) + 1) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (k : ℤ) + 1) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (k : ℤ) + 1) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (k : ℤ) + 1) (by parley_set_side)); parley_set_side)
    -- 3.3. instantiate n := k + 1 in H2, from 3.2
    have s3_3 : 0 ≤ (d ((k : ℤ) + 1) : ℝ) ∧ (d ((k : ℤ) + 1) : ℝ) ≤ 9 := by first | exact (hH2 (k + 1) (by parley_set_side)) | exact ((hH2 (k + 1) (by parley_set_side))).symm | simpa using (hH2 (k + 1) (by parley_set_side)) | exact_mod_cast (hH2 (k + 1) (by parley_set_side)) | (have h := (hH2 (k + 1) (by parley_set_side)); parley_set_side)
    -- 3.4. inequalities
    have s3_4 : 10 * (N (k : ℤ) : ℝ) ≤ 10 * (N (k : ℤ) : ℝ) + (d ((k : ℤ) + 1) : ℝ) := by parley_order
    -- 3.5. transitivity, from 3.4, 3.1
    have s3_5 : 10 * (N (k : ℤ) : ℝ) ≤ (N ((k : ℤ) + 1) : ℝ) := by parley_order
    -- 3.6. inequalities
    have s3_6 : 10 * (N (k : ℤ) : ℝ) + (d ((k : ℤ) + 1) : ℝ) + 1 ≤ 10 * ((N (k : ℤ) : ℝ) + 1) := by parley_order
    -- 3.7. inequalities
    have s3_7 : (N ((k : ℤ) + 1) : ℝ) + 1 = 10 * (N (k : ℤ) : ℝ) + (d ((k : ℤ) + 1) : ℝ) + 1 := by parley_set_side
    -- 3.8. transitivity, from 3.7, 3.6
    have s3_8 : (N ((k : ℤ) + 1) : ℝ) + 1 ≤ 10 * ((N (k : ℤ) : ℝ) + 1) := by parley_order
    -- 3.9. join 3.5, 3.8
    have s3_9 : 10 * (N (k : ℤ) : ℝ) ≤ (N ((k : ℤ) + 1) : ℝ) ∧ (N ((k : ℤ) + 1) : ℝ) + 1 ≤ 10 * ((N (k : ℤ) : ℝ) + 1) := by parley_set_side
    -- 3.10. mun:power-nat a := 10, m := k + 1
    have s3_10 : (0 : ℤ) < 10 ^ (k + 1) := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k + 1)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k + 1))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k + 1)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k + 1)); parley_set_side)
    -- 3.11. mun:exponent-step a := 10, m := k
    have s3_11 : (10 ^ (k + 1) : ℝ) = 10 ^ k * 10 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℝ)) (m := k)); parley_set_side)
    -- 3.12. algebra
    have s3_12 : (N (k : ℤ) : ℝ) / 10 ^ k = 10 * (N (k : ℤ) : ℝ) / (10 ^ k * 10) := by parley_ring
    -- 3.13. substitute 10^(k + 1) = 10^k·10 (line 3.11) into line 3.12
    have s3_13 : (N (k : ℤ) : ℝ) / 10 ^ k = 10 * (N (k : ℤ) : ℝ) / 10 ^ (k + 1) := by
      have e_int : (10 ^ (k + 1) : ℤ) = 10 ^ k * 10 := by exact_mod_cast s3_11
      first | parley_subst_at s3_11 s3_12 | parley_subst_at e_int s3_12
    -- 3.14. algebra
    have s3_14 : ((N (k : ℤ) : ℝ) + 1) / 10 ^ k = 10 * ((N (k : ℤ) : ℝ) + 1) / (10 ^ k * 10) := by parley_ring
    -- 3.15. substitute 10^(k + 1) = 10^k·10 (line 3.11) into line 3.14
    have s3_15 : ((N (k : ℤ) : ℝ) + 1) / 10 ^ k = 10 * ((N (k : ℤ) : ℝ) + 1) / 10 ^ (k + 1) := by
      have e_int : (10 ^ (k + 1) : ℤ) = 10 ^ k * 10 := by exact_mod_cast s3_11
      first | parley_subst_at s3_11 s3_14 | parley_subst_at e_int s3_14
    -- 3.16. mun:divide-le x := 10·N(k), y := N(k + 1), c := 10^(k + 1), from 3.9
    have r254_3 : (10 ^ (k + 1) : ℝ) > 0 := by parley_order
    have s3_16 : 10 * (N (k : ℤ) : ℝ) / 10 ^ (k + 1) ≤ (N ((k : ℤ) + 1) : ℝ) / 10 ^ (k + 1) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N (k : ℤ) : ℝ)) (y := (N ((k : ℤ) + 1) : ℝ)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N (k : ℤ) : ℝ)) (y := (N ((k : ℤ) + 1) : ℝ)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N (k : ℤ) : ℝ)) (y := (N ((k : ℤ) + 1) : ℝ)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N (k : ℤ) : ℝ)) (y := (N ((k : ℤ) + 1) : ℝ)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 3.17. mun:divide-le x := N(k + 1) + 1, y := 10·(N(k) + 1), c := 10^(k + 1), from 3.9
    have r260_3 : (10 ^ (k + 1) : ℝ) > 0 := by parley_order
    have s3_17 : ((N ((k : ℤ) + 1) : ℝ) + 1) / 10 ^ (k + 1) ≤ 10 * ((N (k : ℤ) : ℝ) + 1) / 10 ^ (k + 1) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N ((k : ℤ) + 1) : ℝ) + 1) (y := 10 * ((N (k : ℤ) : ℝ) + 1)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N ((k : ℤ) + 1) : ℝ) + 1) (y := 10 * ((N (k : ℤ) : ℝ) + 1)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N ((k : ℤ) + 1) : ℝ) + 1) (y := 10 * ((N (k : ℤ) : ℝ) + 1)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N ((k : ℤ) + 1) : ℝ) + 1) (y := 10 * ((N (k : ℤ) : ℝ) + 1)) (c := (10 ^ (k + 1) : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 3.18. substitute N(k)/10^k = (10·N(k))/10^(k + 1) (line 3.13) into line 3.16
    have s3_18 : (N (k : ℤ) : ℝ) / 10 ^ k ≤ (N ((k : ℤ) + 1) : ℝ) / 10 ^ (k + 1) := by parley_subst_at s3_13 s3_16
    -- 3.19. substitute (N(k) + 1)/10^k = (10·(N(k) + 1))/10^(k + 1) (line 3.15) into line 3.17
    have s3_19 : ((N ((k : ℤ) + 1) : ℝ) + 1) / 10 ^ (k + 1) ≤ ((N (k : ℤ) : ℝ) + 1) / 10 ^ k := by parley_subst_at s3_15 s3_17
    -- 3.20. calculation
    have s3_20 : L (k : ℤ) ≤ L ((k : ℤ) + 1) := by
      calc L (k : ℤ) = (N (k : ℤ) : ℝ) / 10 ^ k := by first | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side
        _ ≤ (N ((k : ℤ) + 1) : ℝ) / 10 ^ (k + 1) := by parley_set_side
        _ = L ((k : ℤ) + 1) := by first | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side
    -- 3.21. calculation
    have s3_21 : U ((k : ℤ) + 1) ≤ U (k : ℤ) := by
      calc U ((k : ℤ) + 1) = ((N ((k : ℤ) + 1) : ℝ) + 1) / 10 ^ (k + 1) := by first | (simp (disch := omega) only [hD6]; push_cast; norm_num; done) | parley_set_side
        _ ≤ ((N (k : ℤ) : ℝ) + 1) / 10 ^ k := by parley_set_side
        _ = U (k : ℤ) := by first | (simp (disch := omega) only [hD6]; push_cast; norm_num; done) | parley_set_side
    -- 3.22. join 3.20, 3.21
    have s3_22 : L (k : ℤ) ≤ L ((k : ℤ) + 1) ∧ U ((k : ℤ) + 1) ≤ U (k : ℤ) := by parley_set_side
    all_goals exact s3_22
  -- 4. proof
  have s4 : ∀ k : ℕ, (True ∧ True) ∧ L (k : ℤ) ≤ U (k : ℤ) := by
    intro k
    -- 4.1. mun:power-nat a := 10, m := k
    have s4_1 : (0 : ℤ) < 10 ^ k := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := k)); parley_set_side)
    -- 4.2. membership, from D5, 2
    -- 4.3. membership, from D6, 2
    -- 4.4. inequalities
    have s4_4 : (N (k : ℤ) : ℝ) ≤ (N (k : ℤ) : ℝ) + 1 := by parley_order
    -- 4.5. calculation
    have r305_2 : (10 ^ k : ℝ) > 0 := by parley_order
    have s4_5 : L (k : ℤ) ≤ U (k : ℤ) := by
      calc L (k : ℤ) = (N (k : ℤ) : ℝ) / 10 ^ k := by first | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side
        _ ≤ ((N (k : ℤ) : ℝ) + 1) / 10 ^ k := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k : ℤ) : ℝ)) (y := (N (k : ℤ) : ℝ) + 1) (c := (10 ^ k : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k : ℤ) : ℝ)) (y := (N (k : ℤ) : ℝ) + 1) (c := (10 ^ k : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k : ℤ) : ℝ)) (y := (N (k : ℤ) : ℝ) + 1) (c := (10 ^ k : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k : ℤ) : ℝ)) (y := (N (k : ℤ) : ℝ) + 1) (c := (10 ^ k : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
        _ = U (k : ℤ) := by first | (simp (disch := omega) only [hD6]; push_cast; norm_num; done) | parley_set_side
    -- 4.6. join 4.2, 4.3, 4.5
    have s4_6 : L (k : ℤ) ≤ U (k : ℤ) := by parley_set_side
    all_goals parley_set_side
  -- 5. induction on g starting at 0
  have s5 : ∀ g : ℕ, ∀ p : ℕ, L (p : ℤ) ≤ L ((p : ℤ) + (g : ℤ)) ∧ U ((p : ℤ) + (g : ℤ)) ≤ U (p : ℤ) := by
    intro g
    induction g with
    | zero =>
      intro p
      -- 5.1. inequalities, from 4
      have s5_1 : L (p : ℤ) ≤ L (p : ℤ) ∧ U (p : ℤ) ≤ U (p : ℤ) := by have := (s4 p); parley_set_side
      all_goals parley_set_side
    | succ g hIH2 =>
      intro p
      -- 5.2. instantiate p := p in IH2
      have s5_2 : L (p : ℤ) ≤ L ((p : ℤ) + (g : ℤ)) ∧ U ((p : ℤ) + (g : ℤ)) ≤ U (p : ℤ) := by first | exact (hIH2 p) | exact ((hIH2 p)).symm | simpa using (hIH2 p) | exact_mod_cast (hIH2 p) | (have h := (hIH2 p); parley_set_side)
      -- 5.3. instantiate k := p + g in line 3
      have s5_3 : L ((p : ℤ) + (g : ℤ)) ≤ L ((p : ℤ) + (g : ℤ) + 1) ∧ U ((p : ℤ) + (g : ℤ) + 1) ≤ U ((p : ℤ) + (g : ℤ)) := by first | exact (s3 (p + g)) | exact ((s3 (p + g))).symm | simpa using (s3 (p + g)) | exact_mod_cast (s3 (p + g)) | (have h := (s3 (p + g)); parley_set_side)
      -- 5.4. instantiate k := p in line 4
      have s5_4 : L (p : ℤ) ≤ U (p : ℤ) := by first | linarith [(s4 p)] | (have h := (s4 p); push_cast at h; linarith) | exact_mod_cast (s4 p) | (have h := (s4 p); parley_set_side)
      -- 5.5. instantiate k := p + g in line 4
      have s5_5 : L ((p : ℤ) + (g : ℤ)) ≤ U ((p : ℤ) + (g : ℤ)) := by first | linarith [(s4 (p + g))] | (have h := (s4 (p + g)); push_cast at h; linarith) | exact_mod_cast (s4 (p + g)) | (have h := (s4 (p + g)); parley_set_side)
      -- 5.6. instantiate k := (p + g) + 1 in line 4
      have s5_6 : L ((p : ℤ) + (g : ℤ) + 1) ≤ U ((p : ℤ) + (g : ℤ) + 1) := by first | linarith [(s4 (p + g + 1))] | (have h := (s4 (p + g + 1)); push_cast at h; linarith) | exact_mod_cast (s4 (p + g + 1)) | (have h := (s4 (p + g + 1)); parley_set_side)
      -- 5.7. inequalities, from 5.2, 5.4, 5.5
      have s5_7 : L (p : ℤ) ≤ L ((p : ℤ) + (g : ℤ)) := by parley_order
      -- 5.8. inequalities, from 5.3, 5.5, 5.6
      have s5_8 : L ((p : ℤ) + (g : ℤ)) ≤ L ((p : ℤ) + (g : ℤ) + 1) := by parley_order
      -- 5.9. transitivity, from 5.7, 5.8
      have s5_9 : L (p : ℤ) ≤ L ((p : ℤ) + (g : ℤ) + 1) := by parley_order
      -- 5.10. inequalities, from 5.3, 5.5, 5.6
      have s5_10 : U ((p : ℤ) + (g : ℤ) + 1) ≤ U ((p : ℤ) + (g : ℤ)) := by parley_order
      -- 5.11. inequalities, from 5.2, 5.4, 5.5
      have s5_11 : U ((p : ℤ) + (g : ℤ)) ≤ U (p : ℤ) := by parley_order
      -- 5.12. transitivity, from 5.10, 5.11
      have s5_12 : U ((p : ℤ) + (g : ℤ) + 1) ≤ U (p : ℤ) := by parley_order
      -- 5.13. join 5.9, 5.12
      have s5_13 : L (p : ℤ) ≤ L ((p : ℤ) + (g : ℤ) + 1) ∧ U ((p : ℤ) + (g : ℤ) + 1) ≤ U (p : ℤ) := by parley_set_side
      -- 5.14. algebra
      have s5_14 : (p : ℝ) + (g : ℝ) + 1 = (p : ℝ) + ((g : ℝ) + 1) := by parley_ring
      -- 5.15. substitute (p + g) + 1 = p + (g + 1) (line 5.14) into line 5.13
      have s5_15 : L (p : ℤ) ≤ L ((p : ℤ) + ((g : ℤ) + 1)) ∧ U ((p : ℤ) + ((g : ℤ) + 1)) ≤ U (p : ℤ) := by
        have e_int : (p : ℤ) + (g : ℤ) + 1 = (p : ℤ) + ((g : ℤ) + 1) := by exact_mod_cast s5_14
        first | parley_subst_at s5_14 s5_13 | parley_subst_at e_int s5_13
      all_goals parley_set_side
  -- 6. proof
  have s6 : ∀ j : ℕ, ∀ k : ℕ, L (j : ℤ) ≤ U (k : ℤ) := by
    intro j
    intro k
    -- 6.1. instantiate k := j in line 4
    have s6_1 : L (j : ℤ) ≤ U (j : ℤ) := by first | linarith [(s4 j)] | (have h := (s4 j); push_cast at h; linarith) | exact_mod_cast (s4 j) | (have h := (s4 j); parley_set_side)
    -- 6.2. instantiate k := k in line 4
    have s6_2 : L (k : ℤ) ≤ U (k : ℤ) := by first | linarith [(s4 k)] | (have h := (s4 k); push_cast at h; linarith) | exact_mod_cast (s4 k) | (have h := (s4 k); parley_set_side)
    -- 6.3. axi:excluded-middle P := j ≤ k
    have s6_3 : (j : ℝ) ≤ (k : ℝ) ∨ ¬ (j : ℝ) ≤ (k : ℝ) := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (j : ℝ) ≤ (k : ℝ))) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (j : ℝ) ≤ (k : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (j : ℝ) ≤ (k : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (j : ℝ) ≤ (k : ℝ))) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (j : ℝ) ≤ (k : ℝ))); parley_set_side)
    -- 6.4. cases, from 6.3
    have s6_4 : L (j : ℤ) ≤ U (k : ℤ) := by
      rcases s6_3 with hC5 | hC6
      · skip
        -- 6.4.1. mun:nat0-as-int
        have r403_1 : 0 ≤ (k : ℝ) - (j : ℝ) := by parley_set_side
        have s6_4_1 : 0 ≤ (k : ℤ) - (j : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := (k : ℤ) - (j : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := (k : ℤ) - (j : ℤ)))).mpr (by parley_set_side); parley_set_side)
        -- 6.4.2. instantiate g := k − j, p := j in line 5, from 6.4.1
        have s6_4_2 : L (j : ℤ) ≤ L ((j : ℤ) + ((k : ℤ) - (j : ℤ))) ∧ U ((j : ℤ) + ((k : ℤ) - (j : ℤ))) ≤ U (j : ℤ) := by have h := (s5 ((k : ℤ) - (j : ℤ)).toNat j); first | (rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((k : ℤ) - (j : ℤ)) by parley_set_side)] at h; exact h) | (simp (disch := omega) only [← zpow_natCast, Nat.cast_add, Int.toNat_of_nonneg] at h ⊢; exact h)
        -- 6.4.3. substitute
        have s6_4_3 : L (j : ℤ) ≤ L (k : ℤ) ∧ U (k : ℤ) ≤ U (j : ℤ) := by
          have c1 : (j : ℝ) + ((k : ℝ) - (j : ℝ)) = (k : ℝ) := by parley_ring
          have c1_int : (j : ℤ) + ((k : ℤ) - (j : ℤ)) = (k : ℤ) := by exact_mod_cast c1
          have row1 : L (j : ℤ) ≤ L (k : ℤ) ∧ U (k : ℤ) ≤ U (j : ℤ) := by first | parley_subst_at c1 s6_4_2 | parley_subst_at c1_int s6_4_2
          exact row1
        -- 6.4.4. inequalities, from 6.1, 6.2, 6.4.3
        have s6_4_4 : L (j : ℤ) ≤ L (k : ℤ) := by parley_order
        -- 6.4.5. transitivity, from 6.4.4, 6.2
        have s6_4_5 : L (j : ℤ) ≤ U (k : ℤ) := by parley_order
        all_goals parley_set_side
      · skip
        -- 6.4.6. inequalities, from C6
        have s6_4_6 : (k : ℝ) < (j : ℝ) := by parley_order
        -- 6.4.7. inequalities
        have s6_4_7 : 0 ≤ (j : ℝ) - (k : ℝ) := by parley_order
        -- 6.4.8. mun:nat0-as-int
        have r434_1 : 0 ≤ (j : ℝ) - (k : ℝ) := by parley_set_side
        have s6_4_8 : 0 ≤ (j : ℤ) - (k : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := (j : ℤ) - (k : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := (j : ℤ) - (k : ℤ)))).mpr (by parley_set_side); parley_set_side)
        -- 6.4.9. instantiate g := j − k, p := k in line 5, from 6.4.8
        have s6_4_9 : L (k : ℤ) ≤ L ((k : ℤ) + ((j : ℤ) - (k : ℤ))) ∧ U ((k : ℤ) + ((j : ℤ) - (k : ℤ))) ≤ U (k : ℤ) := by have h := (s5 ((j : ℤ) - (k : ℤ)).toNat k); first | (rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((j : ℤ) - (k : ℤ)) by parley_set_side)] at h; exact h) | (simp (disch := omega) only [← zpow_natCast, Nat.cast_add, Int.toNat_of_nonneg] at h ⊢; exact h)
        -- 6.4.10. substitute
        have s6_4_10 : L (k : ℤ) ≤ L (j : ℤ) ∧ U (j : ℤ) ≤ U (k : ℤ) := by
          have c1 : (k : ℝ) + ((j : ℝ) - (k : ℝ)) = (j : ℝ) := by parley_ring
          have c1_int : (k : ℤ) + ((j : ℤ) - (k : ℤ)) = (j : ℤ) := by exact_mod_cast c1
          have row1 : L (k : ℤ) ≤ L (j : ℤ) ∧ U (j : ℤ) ≤ U (k : ℤ) := by first | parley_subst_at c1 s6_4_9 | parley_subst_at c1_int s6_4_9
          exact row1
        -- 6.4.11. inequalities, from 6.1, 6.2, 6.4.10
        have s6_4_11 : U (j : ℤ) ≤ U (k : ℤ) := by parley_order
        -- 6.4.12. transitivity, from 6.1, 6.4.11
        have s6_4_12 : L (j : ℤ) ≤ U (k : ℤ) := by parley_order
        all_goals parley_set_side
    all_goals parley_set_side
  -- 7. mun:set-builder-subset, from D4
  have s7 : S ⊆ (Set.univ : Set ℝ) := by
    try simp only [hD4] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ))); parley_set_side)
  -- 8. proof
  have s8 : ∀ k : ℕ, L (k : ℤ) ∈ S := by
    intro k
    -- 8.1. D5
    have s8_1 : L (k : ℤ) = (N (k : ℤ) : ℝ) / 10 ^ k := by parley_set_side
    -- 8.2. def:set-builder u := L(k), from D4, 8.1
    have s8_2 : L (k : ℤ) ∈ S := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ)) (u := L (k : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ)) (u := L (k : ℤ)))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s8_2
  -- 9. instantiate k := 0 in line 8
  have s9 : L 0 ∈ S := by first | exact (s8 0) | exact ((s8 0)).symm | simpa using (s8 0) | exact_mod_cast (s8 0) | (have h := (s8 0); parley_set_side)
  -- 10. proof
  have s10 : ∀ k : ℕ, ∀ s ∈ S, s ≤ U (k : ℤ) := by
    intro k
    -- 10.1. proof
    have s10_1 : ∀ y ∈ S, y ≤ U (k : ℤ) := by
      intro y hY
      -- 10.1.1. obtain j: def:set-builder u := y, from D4, Y
      obtain ⟨_, j, s10_1_1⟩ := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => ∃ k : ℕ, y = (N (k : ℤ) : ℝ) / 10 ^ k)) (X := (Set.univ : Set ℝ)) (u := y))).mp (by parley_set_side)
      -- 10.1.2. instantiate j := j, k := k in line 6
      have s10_1_2 : L (j : ℤ) ≤ U (k : ℤ) := by first | linarith [(s6 j k)] | (have h := (s6 j k); push_cast at h; linarith) | exact_mod_cast (s6 j k) | (have h := (s6 j k); parley_set_side)
      -- 10.1.3. calculation
      have s10_1_3 : y = L (j : ℤ) := by
        calc y = (N (j : ℤ) : ℝ) / 10 ^ j := by parley_set_side
          _ = L (j : ℤ) := by first | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side
      -- 10.1.4. substitute y = L(j) (line 10.1.3) into line 10.1.2
      have s10_1_4 : y ≤ U (k : ℤ) := by parley_subst_at s10_1_3 s10_1_2
      all_goals exact s10_1_4
    -- 10.2. def:upper-bound, from 10.1
    have s10_2 : ∀ s ∈ S, s ≤ U (k : ℤ) := by parley_set_side
    all_goals exact s10_2
  -- 11. instantiate k := 0 in line 10
  have s11 : ∀ s ∈ S, s ≤ U 0 := by intro s h_s; first | linarith [(s10 0 s (by parley_set_side))] | (have h := (s10 0 s (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s10 0 s (by parley_set_side)) | (have h := (s10 0 s (by parley_set_side)); parley_set_side)
  -- 12. obtain c: axi:completeness, from 7, 9, 11
  obtain ⟨c, ⟨s12, _⟩⟩ := (Parley.Items.Stdlib.Calculus.axi_completeness (S := S) s7 (by parley_set_side) (by parley_set_side))
  -- 13. def:least-upper-bound, from 12
  have s13a : ∀ s ∈ S, s ≤ c := by parley_set_side
  have s13b : ∀ u : ℝ, (∀ s ∈ S, s ≤ u) → c ≤ u := by parley_set_side
  -- 14. def:upper-bound, from 13
  have s14 : ∀ y ∈ S, y ≤ c := by parley_set_side
  -- 15. proof
  have s15 : ∀ k : ℕ, L (k : ℤ) ≤ c ∧ c ≤ U (k : ℤ) := by
    intro k
    -- 15.1. instantiate y := L(k) in line 14, from 8
    have s15_1 : L (k : ℤ) ≤ c := by first | linarith [(s14 (L (k : ℤ)) (by parley_set_side))] | (have h := (s14 (L (k : ℤ)) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s14 (L (k : ℤ)) (by parley_set_side)) | (have h := (s14 (L (k : ℤ)) (by parley_set_side)); parley_set_side)
    -- 15.2. instantiate u := U(k) in line 13, from 10
    have s15_2 : c ≤ U (k : ℤ) := by first | linarith [(s13b (U (k : ℤ)) (by parley_set_side))] | (have h := (s13b (U (k : ℤ)) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s13b (U (k : ℤ)) (by parley_set_side)) | (have h := (s13b (U (k : ℤ)) (by parley_set_side)); parley_set_side)
    -- 15.3. join 15.1, 15.2
    have s15_3 : L (k : ℤ) ≤ c ∧ c ≤ U (k : ℤ) := by parley_set_side
    all_goals exact s15_3
  -- 16. proof
  have s16 : ∀ n : ℕ, 0 < n → ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ) ∨ ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by
    intro n hK6
    -- 16.1. mun:nat-minus-one
    have s16_1 : 0 ≤ (n : ℤ) - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)); parley_set_side)
    -- 16.2. D3
    have r531_1 : 0 ≤ (n : ℤ) - 1 := by parley_set_side
    have s16_2 : (N ((n : ℤ) - 1 + 1) : ℝ) = 10 * (N ((n : ℤ) - 1) : ℝ) + (d ((n : ℤ) - 1 + 1) : ℝ) := by have h := (hD3.2 (((n : ℤ) - 1 + 1) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
    -- 16.3. substitute
    have s16_3 : (N (n : ℤ) : ℝ) = 10 * (N ((n : ℤ) - 1) : ℝ) + (d (n : ℤ) : ℝ) := by
      have c1 : (n : ℝ) - 1 + 1 = (n : ℝ) := by parley_ring
      have c1_int : (n : ℤ) - 1 + 1 = (n : ℤ) := by exact_mod_cast c1
      have row1 : (N (n : ℤ) : ℝ) = 10 * (N ((n : ℤ) - 1) : ℝ) + (d (n : ℤ) : ℝ) := by first | parley_subst_at c1 s16_2 | parley_subst_at c1_int s16_2
      exact row1
    -- 16.4. instantiate k := n − 1 in line 2, from 16.1
    -- 16.5. membership, from 16.3, 16.4
    -- 16.6. mun:power-nat a := 10, m := n
    have s16_6 : (0 : ℤ) < 10 ^ n := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := n)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := n))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := n)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 10) (by parley_set_side) (m := n)); parley_set_side)
    -- 16.7. instantiate k := n in line 15
    have s16_7 : L (n : ℤ) ≤ c ∧ c ≤ U (n : ℤ) := by first | exact (s15 n) | exact ((s15 n)).symm | simpa using (s15 n) | exact_mod_cast (s15 n) | (have h := (s15 n); parley_set_side)
    -- 16.8. mun:multiply-le x := N(n)/10^n, y := c, c := 10^n, from D5, 16.7
    have r553_2 : (10 ^ n : ℝ) > 0 := by parley_order
    have s16_8 : 10 ^ n * ((N (n : ℤ) : ℝ) / 10 ^ n) ≤ 10 ^ n * c := by
      try simp only [hD5] at *
      try push_cast at *
      first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N (n : ℤ) : ℝ) / 10 ^ n) (y := c) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N (n : ℤ) : ℝ) / 10 ^ n) (y := c) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N (n : ℤ) : ℝ) / 10 ^ n) (y := c) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N (n : ℤ) : ℝ) / 10 ^ n) (y := c) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 16.9. mun:multiply-le x := c, y := (N(n) + 1)/10^n, c := 10^n, from D6, 16.7
    have r558_2 : (10 ^ n : ℝ) > 0 := by parley_order
    have s16_9 : 10 ^ n * c ≤ 10 ^ n * (((N (n : ℤ) : ℝ) + 1) / 10 ^ n) := by
      try simp only [hD6] at *
      try push_cast at *
      first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N (n : ℤ) : ℝ) + 1) / 10 ^ n) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N (n : ℤ) : ℝ) + 1) / 10 ^ n) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N (n : ℤ) : ℝ) + 1) / 10 ^ n) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N (n : ℤ) : ℝ) + 1) / 10 ^ n) (c := (10 ^ n : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 16.10. algebra
    have s16_10 : 10 ^ n * ((N (n : ℤ) : ℝ) / 10 ^ n) = (N (n : ℤ) : ℝ) := by parley_ring
    -- 16.11. algebra
    have s16_11 : 10 ^ n * (((N (n : ℤ) : ℝ) + 1) / 10 ^ n) = (N (n : ℤ) : ℝ) + 1 := by parley_ring
    -- 16.12. transitivity, from 16.10, 16.8
    have s16_12 : (N (n : ℤ) : ℝ) ≤ 10 ^ n * c := by parley_order
    -- 16.13. transitivity, from 16.9, 16.11
    have s16_13 : 10 ^ n * c ≤ (N (n : ℤ) : ℝ) + 1 := by parley_order
    -- 16.14. mun:floor-integer x := 10^n·c
    -- 16.15. mun:floor-below x := 10^n·c
    have s16_15 : (⌊10 ^ n * c⌋ : ℝ) ≤ 10 ^ n * c := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n * c))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n * c)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n * c)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n * c)); parley_set_side)
    -- 16.16. mun:floor-above x := 10^n·c
    have s16_16 : 10 ^ n * c < (⌊10 ^ n * c⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n * c))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n * c)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n * c)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n * c)); parley_set_side)
    -- 16.17. transitivity, from 16.12, 16.16
    have s16_17 : (N (n : ℤ) : ℝ) < (⌊10 ^ n * c⌋ : ℝ) + 1 := by parley_order
    -- 16.18. transitivity, from 16.15, 16.13
    have s16_18 : (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ) + 1 := by parley_order
    -- 16.19. mun:integer-step m := N(n), n := ⌊10^n·c⌋ + 1, from 16.5, 16.17
    have s16_19 : (N (n : ℤ) : ℝ) + 1 ≤ (⌊10 ^ n * c⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋ + 1) (by exact_mod_cast s16_17))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋ + 1) (by exact_mod_cast s16_17)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋ + 1) (by exact_mod_cast s16_17)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋ + 1) (by exact_mod_cast s16_17)); parley_set_side)
    -- 16.20. D1
    have s16_20 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) := by parley_set_side
    -- 16.21. mun:nat0-as-int
    have r605_2 : 0 ≤ (d (n : ℤ) : ℝ) := by parley_set_side
    have s16_21 : 0 ≤ d (n : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := d (n : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := d (n : ℤ)))).mpr (by parley_set_side); parley_set_side)
    -- 16.22. membership, from 16.21
    -- 16.23. axi:excluded-middle P := ⌊10^n·c⌋ ≤ N(n)
    have s16_23 : (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ) ∨ ¬ (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ) := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ))) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ))) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (⌊10 ^ n * c⌋ : ℝ) ≤ (N (n : ℤ) : ℝ))); parley_set_side)
    -- 16.24. cases, from 16.23
    have s16_24 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ) ∨ ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by
      rcases s16_23 with hC7 | hC8
      · skip
        -- 16.24.1. inequalities, from 16.19
        have s16_24_1 : (N (n : ℤ) : ℝ) ≤ (⌊10 ^ n * c⌋ : ℝ) := by parley_order
        -- 16.24.2. antisymmetry, from C7, 16.24.1
        have s16_24_2 : (⌊10 ^ n * c⌋ : ℝ) = (N (n : ℤ) : ℝ) := by parley_set_side
        -- 16.24.3. algebra, from 16.3, 16.24.2
        have s16_24_3 : (N ((n : ℤ) - 1) : ℝ) * 10 + (d (n : ℤ) : ℝ) = (⌊10 ^ n * c⌋ : ℝ) := by linear_combination (norm := parley_norm) (-1) * s16_3 + (-1) * s16_24_2
        -- 16.24.4. exhibit, from 16.4, 16.24.3
        have s16_24_4 : ∃ q : ℤ, (q : ℝ) * 10 + (d (n : ℤ) : ℝ) = (⌊10 ^ n * c⌋ : ℝ) := ⟨N ((n : ℤ) - 1), by parley_set_side⟩
        -- 16.24.5. calculation
        have r640_1 : 0 ≤ d (n : ℤ) := by parley_set_side
        have r640_2 : (d (n : ℤ) : ℝ) < 10 := by have := (hH2 n (by parley_set_side)); parley_order
        have s16_24_5 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ) := by
          calc ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) := by parley_set_side
            _ = (d (n : ℤ) : ℝ) := by first | (assumption; done) | (have h : ⌊10 ^ n * c⌋ % (10 : ℤ) = d (n : ℤ) := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := ⌊10 ^ n * c⌋) (m := 10) (by parley_set_side) (r := (d (n : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side)]); parley_set_side)))).mpr (by parley_set_side); exact_mod_cast h) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := ⌊10 ^ n * c⌋) (m := 10) (by parley_set_side) (r := (d (n : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side)]); parley_set_side)))).mpr (by parley_set_side) | (have h := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := ⌊10 ^ n * c⌋) (m := 10) (by parley_set_side) (r := (d (n : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side)]); parley_set_side)))).mpr (by parley_set_side); exact_mod_cast h) | (have h := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := ⌊10 ^ n * c⌋) (m := 10) (by parley_set_side) (r := (d (n : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side)]); parley_set_side)))).mpr (by parley_set_side); simp (disch := parley_set_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); exact_mod_cast h) | (have h := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := ⌊10 ^ n * c⌋) (m := 10) (by parley_set_side) (r := (d (n : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (d (n : ℤ)) by parley_set_side)]); parley_set_side)))).mpr (by parley_set_side); parley_set_side)
        -- 16.24.6. mun:or-left, from 16.24.5
        have s16_24_6 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ) ∨ ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_5)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_5))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_5)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_5)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_5)); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 16.24.7. inequalities, from C8, 16.5, 16.14
        have s16_24_7 : (N (n : ℤ) : ℝ) < (⌊10 ^ n * c⌋ : ℝ) := by parley_order
        -- 16.24.8. mun:integer-step m := N(n), n := ⌊10^n·c⌋, from 16.5, 16.14, 16.24.7
        have s16_24_8 : (N (n : ℤ) : ℝ) + 1 ≤ (⌊10 ^ n * c⌋ : ℝ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋) (by exact_mod_cast s16_24_7))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋) (by exact_mod_cast s16_24_7)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋) (by exact_mod_cast s16_24_7)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N (n : ℤ)) (n := ⌊10 ^ n * c⌋) (by exact_mod_cast s16_24_7)); parley_set_side)
        -- 16.24.9. antisymmetry, from 16.18, 16.24.8
        have s16_24_9 : (⌊10 ^ n * c⌋ : ℝ) = (N (n : ℤ) : ℝ) + 1 := by parley_set_side
        -- 16.24.10. substitute
        have s16_24_10 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((N ((n : ℤ) - 1) * 10 + (d (n : ℤ) + 1)) % (10 : ℤ) : ℤ) : ℝ) := by
          have c1 : (⌊10 ^ n * c⌋ : ℝ) = (N ((n : ℤ) - 1) : ℝ) * 10 + ((d (n : ℤ) : ℝ) + 1) := by linear_combination (norm := parley_norm) s16_3 + s16_24_9
          have c1_int : ⌊10 ^ n * c⌋ = N ((n : ℤ) - 1) * 10 + (d (n : ℤ) + 1) := by exact_mod_cast c1
          have row1 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((N ((n : ℤ) - 1) * 10 + (d (n : ℤ) + 1)) % (10 : ℤ) : ℤ) : ℝ) := by first | parley_subst_at c1 s16_20 | parley_subst_at c1_int s16_20
          exact row1
        -- 16.24.11. D2
        have s16_24_11 : (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by parley_set_side
        -- 16.24.12. calculation
        have s16_24_12 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by
          calc ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((N ((n : ℤ) - 1) * 10 + (d (n : ℤ) + 1)) % (10 : ℤ) : ℤ) : ℝ) := by parley_set_side
            _ = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1)))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d (n : ℤ) + 1) (m := 10) (by parley_set_side) (q := N ((n : ℤ) - 1))); parley_set_side)
            _ = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by parley_set_side
        -- 16.24.13. mun:or-right, from 16.24.12
        have s16_24_13 : ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ) ∨ ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_12)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_12))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_12)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_12)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ)) (Q := ((⌊10 ^ n * c⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) (by exact_mod_cast s16_24_12)); parley_set_side)
        all_goals parley_set_side
    all_goals exact s16_24
  -- 17. exhibit, from 16
  have s17 : ∃ x : ℝ, ∀ n : ℕ, 0 < n → ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) = (d (n : ℤ) : ℝ) ∨ ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) = (((d (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := ⟨c, by parley_set_side⟩
  all_goals exact s17

end Parley.Proofs.Wiedijk.RealsUncountable.DecimalNumber
