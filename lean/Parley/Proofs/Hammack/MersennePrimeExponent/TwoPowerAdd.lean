module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd

theorem two_power_add (a : ℕ) (b : ℕ) :
    (2 ^ (a + b) : ℤ) = 2 ^ a * 2 ^ b := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (2 ^ (a + k) : ℤ) = 2 ^ a * 2 ^ k := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 0 : ℤ) = 1 := by parley_arith
      -- 1.2. substitute 2^0 = 1 (line 1.1)
      have s1_2 : (2 ^ a : ℤ) = 2 ^ a * 2 ^ 0 := by parley_subst s1_1
      all_goals parley_side
    | succ k hIH =>
      -- 1.3. algebra
      have s1_3 : (a : ℤ) + ((k : ℤ) + 1) = (a : ℤ) + (k : ℤ) + 1 := by parley_ring
      -- 1.4. mun:exponent-step a := 2, m := k
      have s1_4 : (2 ^ (k + 1) : ℤ) = 2 ^ k * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); parley_side)
      -- 1.5. calculation
      have s1_5 : (2 ^ (a + (k + 1)) : ℤ) = 2 ^ a * 2 ^ (k + 1) := by
        calc (2 ^ (a + (k + 1)) : ℤ) = 2 ^ (a + k + 1) := by parley_subst s1_3
          _ = 2 ^ (a + k) * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := a + k)); parley_side)
          _ = 2 ^ a * 2 ^ k * 2 := by parley_subst hIH
          _ = 2 ^ a * (2 ^ k * 2) := by parley_ring
          _ = 2 ^ a * 2 ^ (k + 1) := by parley_subst s1_4
      all_goals parley_side
  -- 2. instantiate k := b in line 1
  have s2 : (2 ^ (a + b) : ℤ) = 2 ^ a * 2 ^ b := by first | linear_combination (norm := parley_norm) (s1 b) | (have h := (s1 b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 b) | exact_mod_cast ((s1 b)).symm | (have h := (s1 b); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 b); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 b); parley_int_power h) | (have h := (s1 b); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd
