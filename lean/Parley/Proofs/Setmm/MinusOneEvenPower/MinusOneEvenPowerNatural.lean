module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/minus-one-even-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural

theorem minus_one_even_power_natural (n : ℕ) :
    ((-1) ^ (2 * n) : ℤ) = 1 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, ((-1) ^ (2 * k) : ℤ) = 1 := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : ((-1) ^ (2 * 0) : ℤ) = 1 := by parley_arith
      all_goals parley_side
    | succ k hIH =>
      -- 1.2. algebra
      have s1_2 : 2 * ((k : ℤ) + 1) = 2 * (k : ℤ) + 1 + 1 := by parley_ring
      -- 1.3. calculation
      have s1_3 : ((-1) ^ (2 * k + 1) : ℤ) = -1 := by
        calc ((-1) ^ (2 * k + 1) : ℤ) = (-1) ^ (2 * k) * -1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); parley_side)
          _ = 1 * -1 := by parley_subst hIH
          _ = -1 := by norm_num
      -- 1.4. calculation
      have s1_4 : ((-1) ^ (2 * (k + 1)) : ℤ) = 1 := by
        calc ((-1) ^ (2 * (k + 1)) : ℤ) = (-1) ^ (2 * k + 1 + 1) := by parley_subst s1_2
          _ = (-1) ^ (2 * k + 1) * -1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1)); parley_side)
          _ = -1 * -1 := by parley_subst s1_3
          _ = 1 := by norm_num
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : ((-1) ^ (2 * n) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm | (have h := (s1 n); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); parley_int_power h) | (have h := (s1 n); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural
