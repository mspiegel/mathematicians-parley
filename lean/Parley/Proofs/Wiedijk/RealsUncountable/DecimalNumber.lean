module

public import AlgebraTactics
public import Divisibility
public import Functions
public import OrderTactics
public import PowerTactics
public import RealTactics
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
theorem decimal_number (d : ℤ → ℤ) (hH2 : ∀ n : ℤ, 0 < n → 0 ≤ d n ∧ d n ≤ 9) :
    (∃ x : ℝ, ∀ n : ℤ, 0 < n → ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) = d n ∨ ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) := by
  obtain ⟨N, hD3⟩ : ∃ N : ℤ → ℤ, N 0 = (0 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → N (k + 1) = 10 * N k + d (k + 1) := LeanBridges.Functions.recursion_exists _ (fun k v => 10 * v + d (k + 1))
  set S : Set ℝ := {y : ℝ | ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat} with hD4
  set L : ℤ → ℚ := fun k => (N k : ℚ) / 10 ^ k.toNat with hD5
  set U : ℤ → ℚ := fun k => ((N k : ℚ) + 1) / 10 ^ k.toNat with hD6
  -- 1. D3
  have s1 : N 0 = 0 := by have h := hD3.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
  -- 2. induction on k starting at 0
  -- what this block shows, Lean's types give
  -- 3. proof
  have s3 : ∀ k : ℤ, 0 ≤ k → L k ≤ L (k + 1) ∧ U (k + 1) ≤ U k := by
    intro k hK1
    -- 3.1. D3
    have s3_1 : N (k + 1) = 10 * N k + d (k + 1) := by have h := (hD3.2 ((k + 1) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
    -- 3.2. mun:pos-int-nat
    have r192_1 : 0 < k + 1 := by parley_order
    have s3_2 : 0 < k + 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k + 1) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k + 1) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k + 1) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k + 1) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k + 1) (by parley_set_side)); parley_set_side)
    -- 3.3. instantiate n := k + 1 in H2, from 3.2
    have s3_3 : 0 ≤ d (k + 1) ∧ d (k + 1) ≤ 9 := by first | exact (hH2 (k + 1) (by parley_set_side)) | exact ((hH2 (k + 1) (by parley_set_side))).symm | simpa using (hH2 (k + 1) (by parley_set_side)) | exact_mod_cast (hH2 (k + 1) (by parley_set_side)) | (have h := (hH2 (k + 1) (by parley_set_side)); parley_set_side)
    -- 3.4. inequalities
    have s3_4 : 10 * N k ≤ 10 * N k + d (k + 1) := by parley_order
    -- 3.5. transitivity, from 3.4, 3.1
    have s3_5 : 10 * N k ≤ N (k + 1) := by parley_order
    -- 3.6. inequalities
    have s3_6 : 10 * N k + d (k + 1) + 1 ≤ 10 * (N k + 1) := by parley_order
    -- 3.7. inequalities
    have s3_7 : N (k + 1) + 1 = 10 * N k + d (k + 1) + 1 := by parley_set_side
    -- 3.8. transitivity, from 3.7, 3.6
    have s3_8 : N (k + 1) + 1 ≤ 10 * (N k + 1) := by parley_order
    -- 3.9. join 3.5, 3.8
    have s3_9 : 10 * N k ≤ N (k + 1) ∧ N (k + 1) + 1 ≤ 10 * (N k + 1) := by parley_set_side
    -- 3.10. mun:power-nat a := 10, m := k + 1
    have s3_10 : (0 : ℤ) < 10 ^ (k + 1).toNat := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k + 1) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k + 1) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k + 1) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k + 1) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k + 1) (by parley_set_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k + 1) (by parley_set_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k + 1) (by parley_set_side)); parley_set_side)
    -- 3.11. mun:exponent-step a := 10, m := k
    have s3_11 : (10 ^ (k + 1).toNat : ℤ) = 10 ^ k.toNat * 10 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := k) (by parley_set_side)); parley_set_side)
    -- 3.12. algebra
    have s3_12 : (N k : ℚ) / 10 ^ k.toNat = 10 * (N k : ℚ) / (10 ^ k.toNat * 10) := by parley_ring
    -- 3.13. substitute 10^(k + 1) = 10^k·10 (line 3.11) into line 3.12
    have s3_13 : (N k : ℚ) / 10 ^ k.toNat = 10 * (N k : ℚ) / 10 ^ (k + 1).toNat := by
      have s3_11_w : (10 ^ (k + 1).toNat : ℚ) = 10 ^ k.toNat * 10 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3_11; push_cast at h; linear_combination (norm := parley_norm) h
      first | parley_subst_at s3_11_w s3_12 | parley_subst_at s3_11 s3_12 | (have e_nat : 10 ^ (k + 1).toNat = 10 ^ k.toNat * 10 := by exact_mod_cast s3_11; parley_subst_at e_nat s3_12)
    -- 3.14. algebra
    have s3_14 : ((N k : ℚ) + 1) / 10 ^ k.toNat = 10 * ((N k : ℚ) + 1) / (10 ^ k.toNat * 10) := by parley_ring
    -- 3.15. substitute 10^(k + 1) = 10^k·10 (line 3.11) into line 3.14
    have s3_15 : ((N k : ℚ) + 1) / 10 ^ k.toNat = 10 * ((N k : ℚ) + 1) / 10 ^ (k + 1).toNat := by
      have s3_11_w : (10 ^ (k + 1).toNat : ℚ) = 10 ^ k.toNat * 10 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3_11; push_cast at h; linear_combination (norm := parley_norm) h
      first | parley_subst_at s3_11_w s3_14 | parley_subst_at s3_11 s3_14 | (have e_nat : 10 ^ (k + 1).toNat = 10 ^ k.toNat * 10 := by exact_mod_cast s3_11; parley_subst_at e_nat s3_14)
    -- 3.16. mun:divide-le x := 10·N(k), y := N(k + 1), c := 10^(k + 1), from 3.9
    have r254_3 : (10 ^ (k + 1).toNat : ℤ) > 0 := by parley_order
    have s3_16 : 10 * (N k : ℚ) / 10 ^ (k + 1).toNat ≤ (N (k + 1) : ℚ) / 10 ^ (k + 1).toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N k : ℚ)) (y := (N (k + 1) : ℚ)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N k : ℚ)) (y := (N (k + 1) : ℚ)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N k : ℚ)) (y := (N (k + 1) : ℚ)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N k : ℚ)) (y := (N (k + 1) : ℚ)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 10 * (N k : ℚ)) (y := (N (k + 1) : ℚ)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 3.17. mun:divide-le x := N(k + 1) + 1, y := 10·(N(k) + 1), c := 10^(k + 1), from 3.9
    have r260_3 : (10 ^ (k + 1).toNat : ℤ) > 0 := by parley_order
    have s3_17 : ((N (k + 1) : ℚ) + 1) / 10 ^ (k + 1).toNat ≤ 10 * ((N k : ℚ) + 1) / 10 ^ (k + 1).toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k + 1) : ℚ) + 1) (y := 10 * ((N k : ℚ) + 1)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k + 1) : ℚ) + 1) (y := 10 * ((N k : ℚ) + 1)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k + 1) : ℚ) + 1) (y := 10 * ((N k : ℚ) + 1)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k + 1) : ℚ) + 1) (y := 10 * ((N k : ℚ) + 1)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N (k + 1) : ℚ) + 1) (y := 10 * ((N k : ℚ) + 1)) (c := (10 ^ (k + 1).toNat : ℚ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 3.18. substitute N(k)/10^k = (10·N(k))/10^(k + 1) (line 3.13) into line 3.16
    have s3_18 : (N k : ℚ) / 10 ^ k.toNat ≤ (N (k + 1) : ℚ) / 10 ^ (k + 1).toNat := by parley_subst_at s3_13 s3_16
    -- 3.19. substitute (N(k) + 1)/10^k = (10·(N(k) + 1))/10^(k + 1) (line 3.15) into line 3.17
    have s3_19 : ((N (k + 1) : ℚ) + 1) / 10 ^ (k + 1).toNat ≤ ((N k : ℚ) + 1) / 10 ^ k.toNat := by parley_subst_at s3_15 s3_17
    -- 3.20. calculation
    have s3_20 : L k ≤ L (k + 1) := by
      calc L k = (N k : ℚ) / 10 ^ k.toNat := by first | (simp (disch := omega) only [hD5]; done) | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side | parley_line_toNat hD5
        _ ≤ (N (k + 1) : ℚ) / 10 ^ (k + 1).toNat := by first | parley_set_side | parley_line_toNat s3_18
        _ = L (k + 1) := by first | (simp (disch := omega) only [hD5]; done) | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side | parley_line_toNat hD5
    -- 3.21. calculation
    have s3_21 : U (k + 1) ≤ U k := by
      calc U (k + 1) = ((N (k + 1) : ℚ) + 1) / 10 ^ (k + 1).toNat := by first | (simp (disch := omega) only [hD6]; done) | (simp (disch := omega) only [hD6]; push_cast; norm_num; done) | parley_set_side | parley_line_toNat hD6
        _ ≤ ((N k : ℚ) + 1) / 10 ^ k.toNat := by first | parley_set_side | parley_line_toNat s3_19
        _ = U k := by first | (simp (disch := omega) only [hD6]; done) | (simp (disch := omega) only [hD6]; push_cast; norm_num; done) | parley_set_side | parley_line_toNat hD6
    -- 3.22. join 3.20, 3.21
    have s3_22 : L k ≤ L (k + 1) ∧ U (k + 1) ≤ U k := by parley_set_side
    all_goals exact s3_22
  -- 4. proof
  have s4 : ∀ k : ℤ, 0 ≤ k → (True ∧ True) ∧ L k ≤ U k := by
    intro k hK2
    -- 4.1. mun:power-nat a := 10, m := k
    have s4_1 : (0 : ℤ) < 10 ^ k.toNat := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k) (by parley_set_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k) (by parley_set_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := k) (by parley_set_side)); parley_set_side)
    -- 4.2. membership, from D5, 2
    -- 4.3. membership, from D6, 2
    -- 4.4. inequalities
    have s4_4 : N k ≤ N k + 1 := by parley_order
    -- 4.5. calculation
    have r305_2 : (10 ^ k.toNat : ℤ) > 0 := by parley_order
    have s4_5 : L k ≤ U k := by
      calc L k = (N k : ℚ) / 10 ^ k.toNat := by first | (simp (disch := omega) only [hD5]; done) | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side | parley_line_toNat hD5
        _ ≤ ((N k : ℚ) + 1) / 10 ^ k.toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N k : ℚ)) (y := (N k : ℚ) + 1) (c := (10 ^ k.toNat : ℚ)) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N k : ℚ)) (y := (N k : ℚ) + 1) (c := (10 ^ k.toNat : ℚ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N k : ℚ)) (y := (N k : ℚ) + 1) (c := (10 ^ k.toNat : ℚ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N k : ℚ)) (y := (N k : ℚ) + 1) (c := (10 ^ k.toNat : ℚ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (N k : ℚ)) (y := (N k : ℚ) + 1) (c := (10 ^ k.toNat : ℚ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
        _ = U k := by first | (simp (disch := omega) only [hD6]; done) | (simp (disch := omega) only [hD6]; push_cast; norm_num; done) | parley_set_side | parley_line_toNat hD6
    -- 4.6. join 4.2, 4.3, 4.5
    have s4_6 : L k ≤ U k := by parley_set_side
    all_goals parley_set_side
  -- 5. induction on g starting at 0
  have s5 : ∀ g : ℤ, 0 ≤ g → (∀ p : ℤ, 0 ≤ p → L p ≤ L (p + g) ∧ U (p + g) ≤ U p) := by
    intro g h_g
    replace h_g : 0 ≤ g := by omega
    induction g, h_g using LeanBridges.Functions.le_induction with
    | base =>
      intro p hP1
      -- 5.1. inequalities, from 4
      have s5_1 : L p ≤ L p ∧ U p ≤ U p := by have := (s4 p (by parley_set_side)); parley_set_side
      all_goals parley_set_side
    | succ g hG hIH2 =>
      intro p hP2
      -- 5.2. instantiate p := p in IH2
      have s5_2 : L p ≤ L (p + g) ∧ U (p + g) ≤ U p := by first | exact (hIH2 p (by parley_set_side)) | exact ((hIH2 p (by parley_set_side))).symm | simpa using (hIH2 p (by parley_set_side)) | exact_mod_cast (hIH2 p (by parley_set_side)) | (have h := (hIH2 p (by parley_set_side)); parley_set_side)
      -- 5.3. instantiate k := p + g in line 3
      have s5_3 : L (p + g) ≤ L (p + g + 1) ∧ U (p + g + 1) ≤ U (p + g) := by first | exact (s3 (p + g) (by parley_set_side)) | exact ((s3 (p + g) (by parley_set_side))).symm | simpa using (s3 (p + g) (by parley_set_side)) | exact_mod_cast (s3 (p + g) (by parley_set_side)) | (have h := (s3 (p + g) (by parley_set_side)); parley_set_side)
      -- 5.4. instantiate k := p in line 4
      have s5_4 : L p ≤ U p := by first | linarith [(s4 p (by parley_set_side))] | (have h := (s4 p (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4 p (by parley_set_side)) | (have h := (s4 p (by parley_set_side)); parley_set_side)
      -- 5.5. instantiate k := p + g in line 4
      have s5_5 : L (p + g) ≤ U (p + g) := by first | linarith [(s4 (p + g) (by parley_set_side))] | (have h := (s4 (p + g) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4 (p + g) (by parley_set_side)) | (have h := (s4 (p + g) (by parley_set_side)); parley_set_side)
      -- 5.6. instantiate k := (p + g) + 1 in line 4
      have s5_6 : L (p + g + 1) ≤ U (p + g + 1) := by first | linarith [(s4 (p + g + 1) (by parley_set_side))] | (have h := (s4 (p + g + 1) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4 (p + g + 1) (by parley_set_side)) | (have h := (s4 (p + g + 1) (by parley_set_side)); parley_set_side)
      -- 5.7. inequalities, from 5.2, 5.4, 5.5
      have s5_7 : L p ≤ L (p + g) := by parley_order
      -- 5.8. inequalities, from 5.3, 5.5, 5.6
      have s5_8 : L (p + g) ≤ L (p + g + 1) := by parley_order
      -- 5.9. transitivity, from 5.7, 5.8
      have s5_9 : L p ≤ L (p + g + 1) := by parley_order
      -- 5.10. inequalities, from 5.3, 5.5, 5.6
      have s5_10 : U (p + g + 1) ≤ U (p + g) := by parley_order
      -- 5.11. inequalities, from 5.2, 5.4, 5.5
      have s5_11 : U (p + g) ≤ U p := by parley_order
      -- 5.12. transitivity, from 5.10, 5.11
      have s5_12 : U (p + g + 1) ≤ U p := by parley_order
      -- 5.13. join 5.9, 5.12
      have s5_13 : L p ≤ L (p + g + 1) ∧ U (p + g + 1) ≤ U p := by parley_set_side
      -- 5.14. algebra
      have s5_14 : p + g + 1 = p + (g + 1) := by parley_ring
      -- 5.15. substitute (p + g) + 1 = p + (g + 1) (line 5.14) into line 5.13
      have s5_15 : L p ≤ L (p + (g + 1)) ∧ U (p + (g + 1)) ≤ U p := by parley_subst_at s5_14 s5_13
      all_goals parley_set_side
  -- 6. proof
  have s6 : ∀ j : ℤ, 0 ≤ j → (∀ k : ℤ, 0 ≤ k → L j ≤ U k) := by
    intro j hJ1
    intro k hK3
    -- 6.1. instantiate k := j in line 4
    have s6_1 : L j ≤ U j := by first | linarith [(s4 j (by parley_set_side))] | (have h := (s4 j (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4 j (by parley_set_side)) | (have h := (s4 j (by parley_set_side)); parley_set_side)
    -- 6.2. instantiate k := k in line 4
    have s6_2 : L k ≤ U k := by first | linarith [(s4 k (by parley_set_side))] | (have h := (s4 k (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4 k (by parley_set_side)) | (have h := (s4 k (by parley_set_side)); parley_set_side)
    -- 6.3. axi:excluded-middle P := j ≤ k
    have s6_3 : j ≤ k ∨ ¬ j ≤ k := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j ≤ k)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j ≤ k))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j ≤ k)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j ≤ k)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j ≤ k)); parley_set_side)
    -- 6.4. cases, from 6.3
    have s6_4 : L j ≤ U k := by
      rcases s6_3 with hC5 | hC6
      · skip
        -- 6.4.1. mun:nat0-as-int
        have r403_1 : 0 ≤ k - j := by parley_set_side
        have s6_4_1 : 0 ≤ k - j := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := k - j))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := k - j))).mpr (by parley_set_side); parley_set_side)
        -- 6.4.2. instantiate g := k − j, p := j in line 5, from 6.4.1
        have s6_4_2 : L j ≤ L (j + (k - j)) ∧ U (j + (k - j)) ≤ U j := by first | exact (s5 (k - j) (by parley_set_side) j (by parley_set_side)) | exact ((s5 (k - j) (by parley_set_side) j (by parley_set_side))).symm | simpa using (s5 (k - j) (by parley_set_side) j (by parley_set_side)) | exact_mod_cast (s5 (k - j) (by parley_set_side) j (by parley_set_side)) | (have h := (s5 (k - j) (by parley_set_side) j (by parley_set_side)); parley_set_side)
        -- 6.4.3. substitute
        have s6_4_3 : L j ≤ L k ∧ U k ≤ U j := by
          have c1 : j + (k - j) = k := by parley_ring
          have row1 : L j ≤ L k ∧ U k ≤ U j := by parley_subst_at c1 s6_4_2
          exact row1
        -- 6.4.4. inequalities, from 6.1, 6.2, 6.4.3
        have s6_4_4 : L j ≤ L k := by parley_order
        -- 6.4.5. transitivity, from 6.4.4, 6.2
        have s6_4_5 : L j ≤ U k := by parley_order
        all_goals parley_set_side
      · skip
        -- 6.4.6. inequalities, from C6
        have s6_4_6 : k < j := by parley_order
        -- 6.4.7. inequalities
        have s6_4_7 : 0 ≤ j - k := by parley_order
        -- 6.4.8. mun:nat0-as-int
        have r434_1 : 0 ≤ j - k := by parley_set_side
        have s6_4_8 : 0 ≤ j - k := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := j - k))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := j - k))).mpr (by parley_set_side); parley_set_side)
        -- 6.4.9. instantiate g := j − k, p := k in line 5, from 6.4.8
        have s6_4_9 : L k ≤ L (k + (j - k)) ∧ U (k + (j - k)) ≤ U k := by first | exact (s5 (j - k) (by parley_set_side) k (by parley_set_side)) | exact ((s5 (j - k) (by parley_set_side) k (by parley_set_side))).symm | simpa using (s5 (j - k) (by parley_set_side) k (by parley_set_side)) | exact_mod_cast (s5 (j - k) (by parley_set_side) k (by parley_set_side)) | (have h := (s5 (j - k) (by parley_set_side) k (by parley_set_side)); parley_set_side)
        -- 6.4.10. substitute
        have s6_4_10 : L k ≤ L j ∧ U j ≤ U k := by
          have c1 : k + (j - k) = j := by parley_ring
          have row1 : L k ≤ L j ∧ U j ≤ U k := by parley_subst_at c1 s6_4_9
          exact row1
        -- 6.4.11. inequalities, from 6.1, 6.2, 6.4.10
        have s6_4_11 : U j ≤ U k := by parley_order
        -- 6.4.12. transitivity, from 6.1, 6.4.11
        have s6_4_12 : L j ≤ U k := by parley_order
        all_goals parley_set_side
    all_goals parley_set_side
  -- 7. mun:set-builder-subset, from D4
  have s7 : S ⊆ (Set.univ : Set ℝ) := by
    try simp only [hD4] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ))); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ))); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ))); parley_set_side)
  -- 8. proof
  have s8 : ∀ k : ℤ, 0 ≤ k → (L k : ℝ) ∈ S := by
    intro k hK8
    -- 8.1. D5
    have s8_1 : L k = (N k : ℚ) / 10 ^ k.toNat := by first | (simp (disch := omega) only [hD5]; done) | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side
    -- 8.2. def:set-builder u := L(k), from D4, 8.1
    have s8_2 : (L k : ℝ) ∈ S := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ)) (u := (L k : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ)) (u := (L k : ℝ)))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s8_2
  -- 9. instantiate k := 0 in line 8
  have s9 : (L 0 : ℝ) ∈ S := by first | exact (s8 (0 : ℤ) (by parley_set_side)) | exact ((s8 (0 : ℤ) (by parley_set_side))).symm | simpa using (s8 (0 : ℤ) (by parley_set_side)) | exact_mod_cast (s8 (0 : ℤ) (by parley_set_side)) | (have h := (s8 (0 : ℤ) (by parley_set_side)); parley_set_side)
  -- 10. proof
  have s10 : ∀ k : ℤ, 0 ≤ k → (∀ s ∈ S, s ≤ (U k : ℝ)) := by
    intro k hK4
    -- 10.1. proof
    have s10_1 : ∀ y ∈ S, y ≤ (U k : ℝ) := by
      intro y hY
      -- 10.1.1. obtain j: def:set-builder u := y, from D4, Y
      obtain ⟨_, j, s10_1_1a, s10_1_1b⟩ := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : ℝ => ∃ k : ℤ, 0 ≤ k ∧ y = (N k : ℝ) / 10 ^ k.toNat)) (X := (Set.univ : Set ℝ)) (u := y))).mp (by parley_set_side)
      -- 10.1.2. instantiate j := j, k := k in line 6
      have s10_1_2 : L j ≤ U k := by first | linarith [(s6 j (by parley_set_side) k (by parley_set_side))] | (have h := (s6 j (by parley_set_side) k (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s6 j (by parley_set_side) k (by parley_set_side)) | (have h := (s6 j (by parley_set_side) k (by parley_set_side)); parley_set_side)
      -- 10.1.3. calculation
      have s10_1_3 : y = (L j : ℝ) := by
        calc y = (N j : ℝ) / 10 ^ j.toNat := by first | parley_set_side | parley_line_toNat s10_1_1a | parley_line_toNat s10_1_1b
          _ = (L j : ℝ) := by first | (simp (disch := omega) only [hD5]; done) | (simp (disch := omega) only [hD5]; push_cast; norm_num; done) | parley_set_side | parley_line_toNat hD5
      -- 10.1.4. substitute y = L(j) (line 10.1.3) into line 10.1.2
      have s10_1_4 : y ≤ (U k : ℝ) := by parley_subst_at s10_1_3 s10_1_2
      all_goals exact s10_1_4
    -- 10.2. def:upper-bound, from 10.1
    have s10_2 : ∀ s ∈ S, s ≤ (U k : ℝ) := by parley_set_side
    all_goals exact s10_2
  -- 11. instantiate k := 0 in line 10
  have s11 : ∀ s ∈ S, s ≤ (U 0 : ℝ) := by intro s h_s; first | linarith [(s10 (0 : ℤ) (by parley_set_side) s (by parley_set_side))] | (have h := (s10 (0 : ℤ) (by parley_set_side) s (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s10 (0 : ℤ) (by parley_set_side) s (by parley_set_side)) | (have h := (s10 (0 : ℤ) (by parley_set_side) s (by parley_set_side)); parley_set_side)
  -- 12. obtain c: axi:completeness, from 7, 9, 11
  obtain ⟨c, ⟨s12, _⟩⟩ := (Parley.Items.Stdlib.Calculus.axi_completeness (S := S) s7 (by parley_set_side) (by parley_set_side))
  -- 13. def:least-upper-bound, from 12
  have s13a : ∀ s ∈ S, s ≤ c := by parley_set_side
  have s13b : ∀ u : ℝ, (∀ s ∈ S, s ≤ u) → c ≤ u := by parley_set_side
  -- 14. def:upper-bound, from 13
  have s14 : ∀ y ∈ S, y ≤ c := by parley_set_side
  -- 15. proof
  have s15 : ∀ k : ℤ, 0 ≤ k → (L k : ℝ) ≤ c ∧ c ≤ (U k : ℝ) := by
    intro k hK5
    -- 15.1. instantiate y := L(k) in line 14, from 8
    have s15_1 : (L k : ℝ) ≤ c := by first | linarith [(s14 (L k : ℝ) (by parley_set_side))] | (have h := (s14 (L k : ℝ) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s14 (L k : ℝ) (by parley_set_side)) | (have h := (s14 (L k : ℝ) (by parley_set_side)); parley_set_side)
    -- 15.2. instantiate u := U(k) in line 13, from 10
    have s15_2 : c ≤ (U k : ℝ) := by first | linarith [(s13b (U k : ℝ) (by parley_set_side))] | (have h := (s13b (U k : ℝ) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s13b (U k : ℝ) (by parley_set_side)) | (have h := (s13b (U k : ℝ) (by parley_set_side)); parley_set_side)
    -- 15.3. join 15.1, 15.2
    have s15_3 : (L k : ℝ) ≤ c ∧ c ≤ (U k : ℝ) := by parley_set_side
    all_goals exact s15_3
  -- 16. proof
  have s16 : ∀ n : ℤ, 0 < n → ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n ∨ ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ) := by
    intro n hK6
    -- 16.1. mun:nat-minus-one
    have s16_1 : 0 ≤ n - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side)); parley_set_side)
    -- 16.2. D3
    have r531_1 : 0 ≤ n - 1 := by parley_set_side
    have s16_2 : N (n - 1 + 1) = 10 * N (n - 1) + d (n - 1 + 1) := by have h := (hD3.2 ((n - 1 + 1) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
    -- 16.3. substitute
    have s16_3 : N n = 10 * N (n - 1) + d n := by
      have c1 : n - 1 + 1 = n := by parley_ring
      have row1 : N n = 10 * N (n - 1) + d n := by parley_subst_at c1 s16_2
      exact row1
    -- 16.4. instantiate k := n − 1 in line 2, from 16.1
    -- 16.5. membership, from 16.3, 16.4
    -- 16.6. mun:power-nat a := 10, m := n
    have s16_6 : (0 : ℤ) < 10 ^ n.toNat := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := n) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := n) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := n) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := n) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := n) (by parley_set_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := n) (by parley_set_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (10 : ℤ)) (by parley_set_side) (m := n) (by parley_set_side)); parley_set_side)
    -- 16.7. instantiate k := n in line 15
    have s16_7 : (L n : ℝ) ≤ c ∧ c ≤ (U n : ℝ) := by first | exact (s15 n (by parley_set_side)) | exact ((s15 n (by parley_set_side))).symm | simpa using (s15 n (by parley_set_side)) | exact_mod_cast (s15 n (by parley_set_side)) | (have h := (s15 n (by parley_set_side)); parley_set_side)
    -- 16.8. mun:multiply-le x := N(n)/10^n, y := c, c := 10^n, from D5, 16.7
    have r553_2 : (10 ^ n.toNat : ℤ) > 0 := by parley_order
    have s16_8 : 10 ^ n.toNat * ((N n : ℝ) / 10 ^ n.toNat) ≤ 10 ^ n.toNat * c := by
      try simp only [hD5] at *
      try push_cast at *
      first | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N n : ℝ) / 10 ^ n.toNat) (y := c) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N n : ℝ) / 10 ^ n.toNat) (y := c) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N n : ℝ) / 10 ^ n.toNat) (y := c) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N n : ℝ) / 10 ^ n.toNat) (y := c) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (N n : ℝ) / 10 ^ n.toNat) (y := c) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 16.9. mun:multiply-le x := c, y := (N(n) + 1)/10^n, c := 10^n, from D6, 16.7
    have r558_2 : (10 ^ n.toNat : ℤ) > 0 := by parley_order
    have s16_9 : 10 ^ n.toNat * c ≤ 10 ^ n.toNat * (((N n : ℝ) + 1) / 10 ^ n.toNat) := by
      try simp only [hD6] at *
      try push_cast at *
      first | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N n : ℝ) + 1) / 10 ^ n.toNat) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N n : ℝ) + 1) / 10 ^ n.toNat) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N n : ℝ) + 1) / 10 ^ n.toNat) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N n : ℝ) + 1) / 10 ^ n.toNat) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := c) (y := ((N n : ℝ) + 1) / 10 ^ n.toNat) (c := (10 ^ n.toNat : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 16.10. algebra
    have s16_10 : 10 ^ n.toNat * ((N n : ℚ) / 10 ^ n.toNat) = (N n : ℚ) := by parley_ring
    -- 16.11. algebra
    have s16_11 : 10 ^ n.toNat * (((N n : ℚ) + 1) / 10 ^ n.toNat) = (N n : ℚ) + 1 := by parley_ring
    -- 16.12. transitivity, from 16.10, 16.8
    have s16_12 : (N n : ℝ) ≤ 10 ^ n.toNat * c := by parley_order
    -- 16.13. transitivity, from 16.9, 16.11
    have s16_13 : 10 ^ n.toNat * c ≤ (N n : ℝ) + 1 := by parley_order
    -- 16.14. mun:floor-integer x := 10^n·c
    -- 16.15. mun:floor-below x := 10^n·c
    have s16_15 : (⌊10 ^ n.toNat * c⌋ : ℝ) ≤ 10 ^ n.toNat * c := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n.toNat * c)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n.toNat * c))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n.toNat * c)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n.toNat * c)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := 10 ^ n.toNat * c)); parley_set_side)
    -- 16.16. mun:floor-above x := 10^n·c
    have s16_16 : 10 ^ n.toNat * c < (⌊10 ^ n.toNat * c⌋ : ℝ) + 1 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n.toNat * c)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n.toNat * c))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n.toNat * c)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n.toNat * c)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := 10 ^ n.toNat * c)); parley_set_side)
    -- 16.17. transitivity, from 16.12, 16.16
    have s16_17 : N n < ⌊10 ^ n.toNat * c⌋ + 1 := by parley_order
    -- 16.18. transitivity, from 16.15, 16.13
    have s16_18 : ⌊10 ^ n.toNat * c⌋ ≤ N n + 1 := by parley_order
    -- 16.19. mun:integer-step m := N(n), n := ⌊10^n·c⌋ + 1, from 16.5, 16.17
    have s16_19 : N n + 1 ≤ ⌊10 ^ n.toNat * c⌋ + 1 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋ + 1) s16_17); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋ + 1) s16_17)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋ + 1) s16_17); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋ + 1) s16_17) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋ + 1) s16_17); parley_set_side)
    -- 16.20. D1
    have s16_20 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) := by parley_set_side
    -- 16.21. mun:nat0-as-int
    have r605_2 : 0 ≤ d n := by parley_set_side
    have s16_21 : 0 ≤ d n := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := d n))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := d n))).mpr (by parley_set_side); parley_set_side)
    -- 16.22. membership, from 16.21
    -- 16.23. axi:excluded-middle P := ⌊10^n·c⌋ ≤ N(n)
    have s16_23 : ⌊10 ^ n.toNat * c⌋ ≤ N n ∨ ¬ ⌊10 ^ n.toNat * c⌋ ≤ N n := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := ⌊10 ^ n.toNat * c⌋ ≤ N n)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := ⌊10 ^ n.toNat * c⌋ ≤ N n))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := ⌊10 ^ n.toNat * c⌋ ≤ N n)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := ⌊10 ^ n.toNat * c⌋ ≤ N n)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := ⌊10 ^ n.toNat * c⌋ ≤ N n)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := ⌊10 ^ n.toNat * c⌋ ≤ N n)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := ⌊10 ^ n.toNat * c⌋ ≤ N n)); parley_set_side)
    -- 16.24. cases, from 16.23
    have s16_24 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n ∨ ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ) := by
      rcases s16_23 with hC7 | hC8
      · skip
        -- 16.24.1. inequalities, from 16.19
        have s16_24_1 : N n ≤ ⌊10 ^ n.toNat * c⌋ := by parley_order
        -- 16.24.2. antisymmetry, from C7, 16.24.1
        have s16_24_2 : ⌊10 ^ n.toNat * c⌋ = N n := by parley_set_side
        -- 16.24.3. algebra, from 16.3, 16.24.2
        have s16_24_3 : N (n - 1) * 10 + d n = ⌊10 ^ n.toNat * c⌋ := by linear_combination (norm := parley_norm) (-1) * s16_3 + (-1) * s16_24_2
        -- 16.24.4. exhibit, from 16.4, 16.24.3
        have s16_24_4 : ∃ q : ℤ, q * 10 + d n = ⌊10 ^ n.toNat * c⌋ := ⟨N (n - 1), by parley_set_side⟩
        -- 16.24.5. calculation
        have r640_1 : 0 ≤ d n := by parley_set_side
        have r640_2 : d n < 10 := by have := (hH2 n (by parley_set_side)); parley_order
        have s16_24_5 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n := by
          calc ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) := by first | parley_set_side | parley_line_toNat s16_20
            _ = d n := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := ⌊10 ^ n.toNat * c⌋) (m := (10 : ℤ)) (by parley_set_side) (r := d n) (by parley_set_side) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := ⌊10 ^ n.toNat * c⌋) (m := (10 : ℤ)) (by parley_set_side) (r := d n) (by parley_set_side) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
        -- 16.24.6. mun:or-left, from 16.24.5
        have s16_24_6 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n ∨ ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_5) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_5)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_5) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_5) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_5); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_5); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_5); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 16.24.7. inequalities, from C8, 16.5, 16.14
        have s16_24_7 : N n < ⌊10 ^ n.toNat * c⌋ := by parley_order
        -- 16.24.8. mun:integer-step m := N(n), n := ⌊10^n·c⌋, from 16.5, 16.14, 16.24.7
        have s16_24_8 : N n + 1 ≤ ⌊10 ^ n.toNat * c⌋ := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋) s16_24_7); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋) s16_24_7)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋) s16_24_7); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋) s16_24_7) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N n) (n := ⌊10 ^ n.toNat * c⌋) s16_24_7); parley_set_side)
        -- 16.24.9. antisymmetry, from 16.18, 16.24.8
        have s16_24_9 : ⌊10 ^ n.toNat * c⌋ = N n + 1 := by parley_set_side
        -- 16.24.10. substitute
        have s16_24_10 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (N (n - 1) * 10 + (d n + 1)) % (10 : ℤ) := by
          have c1 : ⌊10 ^ n.toNat * c⌋ = N (n - 1) * 10 + (d n + 1) := by linear_combination (norm := parley_norm) s16_3 + s16_24_9
          have row1 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (N (n - 1) * 10 + (d n + 1)) % (10 : ℤ) := by parley_subst_at c1 s16_20
          exact row1
        -- 16.24.11. D2
        have s16_24_11 : (d n + 1) % (10 : ℤ) = (d n + 1) % (10 : ℤ) := by parley_set_side
        -- 16.24.12. calculation
        have s16_24_12 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ) := by
          calc ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (N (n - 1) * 10 + (d n + 1)) % (10 : ℤ) := by first | parley_set_side | parley_line_toNat s16_24_10
            _ = (d n + 1) % (10 : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1)))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := d n + 1) (m := (10 : ℤ)) (by parley_set_side) (q := N (n - 1))); parley_set_side)
            _ = (d n + 1) % (10 : ℤ) := by parley_set_side
        -- 16.24.13. mun:or-right, from 16.24.12
        have s16_24_13 : ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n ∨ ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_12) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_12)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_12) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_12) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_12); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_12); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = d n) (Q := ⌊10 ^ n.toNat * c⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ)) s16_24_12); parley_set_side)
        all_goals parley_set_side
    all_goals exact s16_24
  -- 17. exhibit, from 16
  have s17 : ∃ x : ℝ, ∀ n : ℤ, 0 < n → ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) = d n ∨ ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) = (d n + 1) % (10 : ℤ) := ⟨c, by parley_set_side⟩
  all_goals exact s17

end Parley.Proofs.Wiedijk.RealsUncountable.DecimalNumber
