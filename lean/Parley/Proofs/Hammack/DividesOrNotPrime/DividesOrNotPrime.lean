module

public import ArithTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/divides-or-not-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesOrNotPrime.DividesOrNotPrime

set_option maxHeartbeats 400000 in
theorem divides_or_not_prime (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (hH3 : (Int.gcd a b : ℤ) > 1) :
    (b ∣ a ∨ ¬ Nat.Prime b.toNat) := by
  -- the theorem. contradiction
  have sThm : b ∣ a ∨ ¬ Nat.Prime b.toNat := by
    by_contra hc_hS
    have hS : ¬ (b ∣ a ∨ ¬ Nat.Prime b.toNat) := by parley_suppose hc_hS
    -- 1. mun:not-either, from S
    have s1a : ¬ b ∣ a := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).1; simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).1; simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).1; parley_side)
    have s1b : ¬ ¬ Nat.Prime b.toNat := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).2; simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).2; simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp (by parley_side)).2; parley_side)
    -- 2. mun:double-negation, from 1
    have s2 : Nat.Prime b.toNat := by first | exact (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b) | exact ((Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b); parley_side)
    -- 3. def:prime p := b, from 2
    have s3a : b > 1 := by first | linarith [(((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).1] | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).1; parley_side)
    have s3b : ∀ d : ℤ, 0 < d → d ∣ b → d = 1 ∨ d = b := by first | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp (by parley_side)).2; parley_side)
    -- 4. def:gcd
    have s4a : 0 < (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
    have s4b : (Int.gcd a b : ℤ) ∣ b := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
    -- 5. instantiate d := gcd(a, b) in line 3, from 4
    have s5 : (Int.gcd a b : ℤ) ∣ b → (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b := by first | exact (s3b (Int.gcd a b : ℤ) (by parley_side)) | exact ((s3b (Int.gcd a b : ℤ) (by parley_side))).symm | simpa using (s3b (Int.gcd a b : ℤ) (by parley_side)) | exact_mod_cast (s3b (Int.gcd a b : ℤ) (by parley_side)) | (have h := (s3b (Int.gcd a b : ℤ) (by parley_side)); parley_side)
    -- 6. mun:modus-ponens P := gcd(a, b) divides b, from 4, 5
    have s6 : (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (Int.gcd a b : ℤ) ∣ b) (Q := (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b) s5 s4b) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (Int.gcd a b : ℤ) ∣ b) (Q := (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b) s5 s4b)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (Int.gcd a b : ℤ) ∣ b) (Q := (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b) s5 s4b) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (Int.gcd a b : ℤ) ∣ b) (Q := (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b) s5 s4b) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (Int.gcd a b : ℤ) ∣ b) (Q := (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b) s5 s4b); parley_side)
    -- 7. def:gcd
    have s7 : (Int.gcd a b : ℤ) ∣ a := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
    -- 8. cases, from 6
    have s8 : b ∣ a := by
      rcases s6 with hC1 | hC2
      · skip
        -- 8.1. inequalities
        have s8_1 : (Int.gcd a b : ℤ) ≠ 1 := by parley_side
        all_goals parley_side
      · skip
        -- 8.2. substitute gcd(a, b) = b (C2) into line 7
        have s8_2 : b ∣ a := by parley_subst_at hC2 s7
        all_goals parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.DividesOrNotPrime.DividesOrNotPrime
