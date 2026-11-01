module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

theorem even_power_of_minus_one (k : ℕ) :
    ((-1) ^ (2 * k) : ℤ) = 1 := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℕ, ((-1) ^ (2 * j) : ℤ) = 1 := by
    intro j
    induction j with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : ((-1) ^ (2 * 0) : ℤ) = 1 := by parley_arith
      all_goals parley_side
    | succ j hIH =>
      -- 1.2. algebra
      have s1_2 : 2 * ((j : ℤ) + 1) = 2 * (j : ℤ) + 2 := by parley_ring
      -- 1.3. calculation
      have s1_3 : ((-1) ^ (2 * (j + 1)) : ℤ) = 1 := by
        calc ((-1) ^ (2 * (j + 1)) : ℤ) = (-1) ^ (2 * j + 2) := by parley_subst s1_2
          _ = (-1) ^ (2 * j) * (-1) ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (n := 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (n := 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (n := 2)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (n := 2))).symm
          _ = 1 * (-1) ^ 2 := by parley_subst hIH
          _ = 1 := by norm_num
      all_goals parley_side
  -- 2. instantiate j := k in line 1
  have s2 : ((-1) ^ (2 * k) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (s1 k) | (have h := (s1 k); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (s1 k) | exact_mod_cast ((s1 k)).symm
  all_goals parley_side

end Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne
