module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd

theorem two_power_add (a : ℤ) (hH1 : 0 ≤ a) (b : ℤ) (hH2 : 0 ≤ b) :
    (2 ^ (a + b).toNat : ℤ) = 2 ^ a.toNat * 2 ^ b.toNat := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (2 ^ (a + k).toNat : ℤ) = 2 ^ a.toNat * 2 ^ k.toNat := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 0 : ℤ) = 1 := by parley_arith
      -- 1.2. substitute 2^0 = 1 (line 1.1)
      have s1_2 : (2 ^ a.toNat : ℤ) = 2 ^ a.toNat * 2 ^ 0 := by parley_subst s1_1
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.3. algebra
      have s1_3 : a + (k + 1) = a + k + 1 := by parley_ring
      -- 1.4. mun:exponent-step a := 2, m := k
      have s1_4 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); parley_side)
      -- 1.5. calculation
      have s1_5 : (2 ^ (a + (k + 1)).toNat : ℤ) = 2 ^ a.toNat * 2 ^ (k + 1).toNat := by
        calc (2 ^ (a + (k + 1)).toNat : ℤ) = 2 ^ (a + k + 1).toNat := by parley_subst s1_3
          _ = 2 ^ (a + k).toNat * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k) (by parley_side)); parley_side)
          _ = 2 ^ a.toNat * 2 ^ k.toNat * 2 := by parley_subst hIH
          _ = 2 ^ a.toNat * (2 ^ k.toNat * 2) := by parley_ring
          _ = 2 ^ a.toNat * 2 ^ (k + 1).toNat := by parley_subst s1_4
      all_goals parley_side
  -- 2. instantiate k := b in line 1
  have s2 : (2 ^ (a + b).toNat : ℤ) = 2 ^ a.toNat * 2 ^ b.toNat := by first | linear_combination (norm := parley_norm) (s1 b (by parley_side)) | (have h := (s1 b (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 b (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 b (by parley_side)) | exact_mod_cast ((s1 b (by parley_side))).symm | (have h := (s1 b (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 b (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 b (by parley_side)); parley_int_power h) | (have h := (s1 b (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 b (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 b (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd
