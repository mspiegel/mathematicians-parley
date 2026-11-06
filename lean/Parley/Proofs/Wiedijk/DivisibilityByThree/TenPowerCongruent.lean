module

public import Functions
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

/-! Written from proofs/wiedijk/divisibility-by-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent

theorem ten_power_congruent (k : ℤ) (hH1 : 0 ≤ k) :
    (10 ^ k.toNat : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → (10 ^ m.toNat : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (10 ^ 0 : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
        calc (10 ^ 0 : ℤ) = 1 := by norm_num
          _ ≡ 1 [ZMOD (3 : ℤ)] := by norm_num
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.2. mun:exponent-step a := 10
      have s1_2 : (10 ^ (m + 1).toNat : ℤ) = 10 ^ m.toNat * 10 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side)); parley_side)
      -- 1.3. calculation
      have s1_3 : (10 ^ (m + 1).toNat : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
        calc (10 ^ (m + 1).toNat : ℤ) = 10 ^ m.toNat * 10 := by first | parley_side | parley_line_toNat s1_2
          _ ≡ 1 * 10 [ZMOD (3 : ℤ)] := by first | exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH) | exact ((Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH)).symm | simpa using (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH) | exact_mod_cast (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH); parley_side)
          _ ≡ 10 [ZMOD (3 : ℤ)] := by norm_num
          _ ≡ 1 [ZMOD (3 : ℤ)] := by norm_num
      all_goals parley_side
  -- 2. instantiate m := k in line 1
  have s2 : (10 ^ k.toNat : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by first | exact (s1 k (by parley_side)) | exact ((s1 k (by parley_side))).symm | simpa using (s1 k (by parley_side)) | exact_mod_cast (s1 k (by parley_side)) | (have h := (s1 k (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 k (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent
