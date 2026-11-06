module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/minus-one-even-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural

theorem minus_one_even_power_natural (n : ℤ) (hH1 : 0 ≤ n) :
    ((-1) ^ (2 * n).toNat : ℤ) = 1 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → ((-1) ^ (2 * k).toNat : ℤ) = 1 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : ((-1) ^ (2 * 0) : ℤ) = 1 := by parley_arith
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. algebra
      have s1_2 : 2 * (k + 1) = 2 * k + 1 + 1 := by parley_ring
      -- 1.3. calculation
      have s1_3 : ((-1) ^ (2 * k + 1).toNat : ℤ) = -1 := by
        calc ((-1) ^ (2 * k + 1).toNat : ℤ) = (-1) ^ (2 * k).toNat * -1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); parley_side)
          _ = 1 * -1 := by parley_subst hIH
          _ = -1 := by norm_num
      -- 1.4. calculation
      have s1_4 : ((-1) ^ (2 * (k + 1)).toNat : ℤ) = 1 := by
        calc ((-1) ^ (2 * (k + 1)).toNat : ℤ) = (-1) ^ (2 * k + 1 + 1).toNat := by parley_subst s1_2
          _ = (-1) ^ (2 * k + 1).toNat * -1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side)); parley_side)
          _ = -1 * -1 := by parley_subst s1_3
          _ = 1 := by norm_num
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : ((-1) ^ (2 * n).toNat : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural
