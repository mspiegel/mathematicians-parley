module

public import ArithTactics
public import Divisibility
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/wiedijk/euclid.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Euclid.Euclid

set_option maxHeartbeats 1200000 in
theorem euclid (M : ℤ) (hH1 : 0 ≤ M) (N : ℤ) (hH2 : 0 ≤ N) (a : ℤ → ℤ) (b : ℤ → ℤ) (hD1 : a 0 = M ∧ b 0 = N ∧ ∀ k : ℤ, 0 ≤ k → a (k + 1) = @ite _ (b k = 0) (Classical.propDecidable (b k = 0)) (a k) (b k) ∧ b (k + 1) = @ite _ (b k = 0) (Classical.propDecidable (b k = 0)) 0 (a k % b k)) :
    a N = (Int.gcd M N : ℤ) := by
  -- 1. D1
  have s1 : a 0 = M := by have h := hD1.1; (try ring_nf at h ⊢); linarith
  -- 2. D1
  have s2 : b 0 = N := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
  -- 3. induction on k starting at 0
  have s3 : ∀ k : ℤ, 0 ≤ k → 0 ≤ a k ∧ 0 ≤ b k := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 3.1. substitute a(0) = M (line 1) into H1
      have s3_1 : 0 ≤ a 0 := by parley_subst_at s1 hH1
      -- 3.2. substitute b(0) = N (line 2) into H2
      have s3_2 : 0 ≤ b 0 := by parley_subst_at s2 hH2
      -- 3.3. join 3.1, 3.2
      have s3_3 : 0 ≤ a 0 ∧ 0 ≤ b 0 := by parley_side
      all_goals parley_side
    | succ k hK1 hIH1 =>
      -- 3.4. axi:excluded-middle P := b(k) = 0
      have s3_4 : b k = 0 ∨ b k ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)); parley_side)
      -- 3.5. cases, from 3.4
      have s3_5 : 0 ≤ a (k + 1) ∧ 0 ≤ b (k + 1) := by
        rcases s3_4 with hC1 | hC2
        · skip
          -- 3.5.1. D1, from C1
          have s3_5_1 : a (k + 1) = a k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).1; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_left hC1] at h; (try ring_nf at h ⊢); linarith
          -- 3.5.2. D1, from C1
          have s3_5_2 : b (k + 1) = 0 := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_left hC1] at h; (try ring_nf at h ⊢); linarith
          -- 3.5.3. substitute a(k + 1) = a(k) (line 3.5.1) into IH1
          have s3_5_3 : 0 ≤ a (k + 1) := by parley_subst_at s3_5_1 hIH1
          -- 3.5.4. membership, from 3.5.2
          have s3_5_4 : 0 ≤ b (k + 1) := by parley_side
          -- 3.5.5. join 3.5.3, 3.5.4
          have s3_5_5 : 0 ≤ a (k + 1) ∧ 0 ≤ b (k + 1) := by parley_side
          all_goals parley_side
        · skip
          -- 3.5.6. D1, from C2
          have s3_5_6 : a (k + 1) = b k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).1; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_right hC2] at h; (try ring_nf at h ⊢); linarith
          -- 3.5.7. D1, from C2
          have s3_5_7 : b (k + 1) = a k % b k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_right hC2] at h; (try ring_nf at h ⊢); linarith
          -- 3.5.8. mun:nat0-nonzero, from C2, IH1
          have s3_5_8 : 0 < b k := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC2) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC2)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC2) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC2) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC2); parley_side)
          -- 3.5.9. mun:mod-natural, from 3.5.8
          have s3_5_9 : 0 ≤ a k % b k := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)); parley_side)
          -- 3.5.10. substitute a(k + 1) = b(k) (line 3.5.6) into IH1
          have s3_5_10 : 0 ≤ a (k + 1) := by parley_subst_at s3_5_6 hIH1
          -- 3.5.11. substitute b(k + 1) = a(k) mod b(k) (line 3.5.7) into line 3.5.9
          have s3_5_11 : 0 ≤ b (k + 1) := by parley_subst_at s3_5_7 s3_5_9
          -- 3.5.12. join 3.5.10, 3.5.11
          have s3_5_12 : 0 ≤ a (k + 1) ∧ 0 ≤ b (k + 1) := by parley_side
          all_goals parley_side
      all_goals parley_side
  -- 4. induction on k starting at 0
  have s4 : ∀ k : ℤ, 0 ≤ k → (Int.gcd (a k) (b k) : ℤ) = (Int.gcd M N : ℤ) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 4.1. calculation
      have s4_1 : (Int.gcd (a 0) (b 0) : ℤ) = (Int.gcd M N : ℤ) := by
        calc (Int.gcd (a 0) (b 0) : ℤ) = (Int.gcd M (b 0) : ℤ) := by parley_subst s1
          _ = (Int.gcd M N : ℤ) := by parley_subst s2
      all_goals parley_side
    | succ k hK2 hIH2 =>
      -- 4.2. axi:excluded-middle P := b(k) = 0
      have s4_2 : b k = 0 ∨ b k ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)); parley_side)
      -- 4.3. cases, from 4.2
      have s4_3 : (Int.gcd (a (k + 1)) (b (k + 1)) : ℤ) = (Int.gcd M N : ℤ) := by
        rcases s4_2 with hC3 | hC4
        · skip
          -- 4.3.1. D1, from C3
          have s4_3_1 : a (k + 1) = a k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).1; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_left hC3] at h; (try ring_nf at h ⊢); linarith
          -- 4.3.2. D1, from C3
          have s4_3_2 : b (k + 1) = 0 := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_left hC3] at h; (try ring_nf at h ⊢); linarith
          -- 4.3.3. calculation
          have s4_3_3 : (Int.gcd (a (k + 1)) (b (k + 1)) : ℤ) = (Int.gcd M N : ℤ) := by
            calc (Int.gcd (a (k + 1)) (b (k + 1)) : ℤ) = (Int.gcd (a k) (b (k + 1)) : ℤ) := by parley_subst s4_3_1
              _ = (Int.gcd (a k) (0 : ℤ) : ℤ) := by parley_subst s4_3_2
              _ = (Int.gcd (a k) (b k) : ℤ) := by parley_subst hC3
              _ = (Int.gcd M N : ℤ) := by parley_side
          all_goals parley_side
        · skip
          -- 4.3.4. D1, from C4
          have s4_3_4 : a (k + 1) = b k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).1; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_right hC4] at h; (try ring_nf at h ⊢); linarith
          -- 4.3.5. D1, from C4
          have s4_3_5 : b (k + 1) = a k % b k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_right hC4] at h; (try ring_nf at h ⊢); linarith
          -- 4.3.6. mun:nat0-nonzero, from C4, 3
          have s4_3_6 : 0 < b k := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC4) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC4)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC4) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC4) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC4); parley_side)
          -- 4.3.7. mun:nat0-int, from 3
          -- 4.3.8. mun:gcd-commutes
          have r155_2 : 0 ≤ a k % b k := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)); parley_side)
          have s4_3_8 : (Int.gcd (b k) (a k % b k) : ℤ) = (Int.gcd (a k % b k) (b k) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := b k) (b := a k % b k)); parley_side)
          -- 4.3.9. calculation
          have s4_3_9 : (Int.gcd (a (k + 1)) (b (k + 1)) : ℤ) = (Int.gcd M N : ℤ) := by
            calc (Int.gcd (a (k + 1)) (b (k + 1)) : ℤ) = (Int.gcd (b k) (b (k + 1)) : ℤ) := by parley_subst s4_3_4
              _ = (Int.gcd (b k) (a k % b k) : ℤ) := by parley_subst s4_3_5
              _ = (Int.gcd (a k % b k) (b k) : ℤ) := by parley_side
              _ = (Int.gcd (a k) (b k) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a k) (b := b k) (by parley_side)); parley_side)
              _ = (Int.gcd M N : ℤ) := by parley_side
          all_goals parley_side
      all_goals parley_side
  -- 5. induction on k starting at 0
  have s5 : ∀ k : ℤ, 0 ≤ k → b k + k ≤ N ∨ b k = 0 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 5.1. inequalities
      have s5_1 : b 0 ≤ N := by parley_order
      -- 5.2. mun:or-left, from 5.1
      have s5_2 : b 0 ≤ N ∨ b 0 = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b 0 ≤ N) (Q := b 0 = 0) s5_1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := b 0 ≤ N) (Q := b 0 = 0) s5_1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b 0 ≤ N) (Q := b 0 = 0) s5_1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b 0 ≤ N) (Q := b 0 = 0) s5_1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b 0 ≤ N) (Q := b 0 = 0) s5_1); parley_side)
      all_goals parley_side
    | succ k hK3 hIH3 =>
      -- 5.3. axi:excluded-middle P := b(k) = 0
      have s5_3 : b k = 0 ∨ b k ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b k = 0)); parley_side)
      -- 5.4. cases, from 5.3
      have s5_4 : b (k + 1) + (k + 1) ≤ N ∨ b (k + 1) = 0 := by
        rcases s5_3 with hC5 | hC6
        · skip
          -- 5.4.1. D1, from C5
          have s5_4_1 : b (k + 1) = 0 := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_left hC5] at h; (try ring_nf at h ⊢); linarith
          -- 5.4.2. mun:or-right, from 5.4.1
          have s5_4_2 : b (k + 1) + (k + 1) ≤ N ∨ b (k + 1) = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_1); parley_side)
          all_goals parley_side
        · skip
          -- 5.4.3. D1, from C6
          have s5_4_3 : b (k + 1) = a k % b k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel, add_sub_cancel_right] at h; rw [ite_eq_right hC6] at h; (try ring_nf at h ⊢); linarith
          -- 5.4.4. mun:nat0-nonzero, from C6, 3
          have s5_4_4 : 0 < b k := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC6) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC6)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC6) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC6) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b k) (by parley_side) hC6); parley_side)
          -- 5.4.5. mun:nat0-int, from 3
          -- 5.4.6. mun:mod-less, from 5.4.4, 5.4.5
          have s5_4_6 : a k % b k < b k := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a k) (b := b k) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a k) (b := b k) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a k) (b := b k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a k) (b := b k) (by parley_side)); parley_side)
          -- 5.4.7. mun:mod-natural, from 5.4.4, 5.4.5
          have s5_4_7 : 0 ≤ a k % b k := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a k) (b := b k) (by parley_side)); parley_side)
          -- 5.4.8. substitute b(k + 1) = a(k) mod b(k) (line 5.4.3) into line 5.4.6
          have s5_4_8 : b (k + 1) < b k := by parley_subst_at s5_4_3 s5_4_6
          -- 5.4.9. substitute b(k + 1) = a(k) mod b(k) (line 5.4.3) into line 5.4.7
          have s5_4_9 : 0 ≤ b (k + 1) := by parley_subst_at s5_4_3 s5_4_7
          -- 5.4.10. mun:integer-step, from 5.4.8
          have s5_4_10 : b (k + 1) + 1 ≤ b k := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := b (k + 1)) (n := b k) s5_4_8)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := b (k + 1)) (n := b k) s5_4_8); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := b (k + 1)) (n := b k) s5_4_8) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := b (k + 1)) (n := b k) s5_4_8); parley_side)
          -- 5.4.11. mun:disjunctive-syllogism, from C6, IH3
          have s5_4_11 : b k + k ≤ N := by first | linarith [(Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b k + k ≤ N) (Q := b k = 0) hIH3 hC6)] | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b k + k ≤ N) (Q := b k = 0) hIH3 hC6); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b k + k ≤ N) (Q := b k = 0) hIH3 hC6) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b k + k ≤ N) (Q := b k = 0) hIH3 hC6); parley_side)
          -- 5.4.12. inequalities
          have s5_4_12 : b (k + 1) + (k + 1) ≤ b k + k := by parley_order
          -- 5.4.13. transitivity, from 5.4.12, 5.4.11
          have s5_4_13 : b (k + 1) + (k + 1) ≤ N := by parley_order
          -- 5.4.14. mun:or-left, from 5.4.13
          have s5_4_14 : b (k + 1) + (k + 1) ≤ N ∨ b (k + 1) = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_13) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_13)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_13) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_13) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b (k + 1) + (k + 1) ≤ N) (Q := b (k + 1) = 0) s5_4_13); parley_side)
          all_goals parley_side
      all_goals parley_side
  -- 6. instantiate k := N in line 3
  have s6 : 0 ≤ a N ∧ 0 ≤ b N := by first | exact (s3 N (by parley_side)) | exact ((s3 N (by parley_side))).symm | simpa using (s3 N (by parley_side)) | exact_mod_cast (s3 N (by parley_side)) | (have h := (s3 N (by parley_side)); parley_side)
  -- 7. instantiate k := N in line 5
  have s7 : b N + N ≤ N ∨ b N = 0 := by first | exact (s5 N (by parley_side)) | exact ((s5 N (by parley_side))).symm | simpa using (s5 N (by parley_side)) | exact_mod_cast (s5 N (by parley_side)) | (have h := (s5 N (by parley_side)); parley_side)
  -- 8. contradiction
  have s8 : b N = 0 := by
    by_contra hc_hS
    have hS : b N ≠ 0 := by parley_suppose hc_hS
    -- 8.1. mun:disjunctive-syllogism, from S, 7
    have s8_1 : b N + N ≤ N := by first | linarith [(Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b N + N ≤ N) (Q := b N = 0) s7 hS)] | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b N + N ≤ N) (Q := b N = 0) s7 hS); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b N + N ≤ N) (Q := b N = 0) s7 hS) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := b N + N ≤ N) (Q := b N = 0) s7 hS); parley_side)
    -- 8.2. mun:nat0-nonzero, from S, 6
    have s8_2 : 0 < b N := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b N) (by parley_side) hS) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b N) (by parley_side) hS)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b N) (by parley_side) hS) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b N) (by parley_side) hS) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := b N) (by parley_side) hS); parley_side)
    -- 8.3. inequalities, from 8.2
    have s8_3 : ¬ b N + N ≤ N := by parley_side
    all_goals parley_side
  -- 9. calculation
  have s9 : a N = (Int.gcd M N : ℤ) := by
    calc a N = (Int.gcd (a N) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := a N) (by parley_side)); parley_side)
      _ = (Int.gcd (a N) (b N) : ℤ) := by parley_subst s8
      _ = (Int.gcd M N : ℤ) := by first | linear_combination (norm := parley_norm) (s4 N (by parley_side)) | (have h := (s4 N (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s4 N (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s4 N (by parley_side)) | exact_mod_cast ((s4 N (by parley_side))).symm | (have h := (s4 N (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s4 N (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s4 N (by parley_side)); parley_int_power h) | (have h := (s4 N (by parley_side)); parley_side)
  all_goals exact s9

end Parley.Proofs.Wiedijk.Euclid.Euclid
