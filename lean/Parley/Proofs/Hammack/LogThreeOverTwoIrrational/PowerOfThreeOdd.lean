module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/log-three-over-two-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd

theorem power_of_three_odd (n : ℕ) :
    Odd (3 ^ n : ℤ) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℕ, Odd (3 ^ j : ℤ) := by
    intro j
    induction j with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (3 ^ 0 : ℤ) = 2 * 0 + 1 := by parley_arith
      -- 1.2. def:odd n := 3^0, from 1.1
      have s1_2 : Odd (3 ^ 0 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ 0 : ℤ)))).mpr ⟨(0 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ 0 : ℤ)))).mpr ⟨(0 : ℤ), by parley_side⟩; parley_side)
      all_goals parley_side
    | succ j hIH =>
      -- 1.3. obtain k: def:odd n := 3^j, from IH
      obtain ⟨k, s1_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ j : ℤ)))).mp (by parley_side)
      -- 1.4. calculation
      have s1_4 : 3 ^ (j + 1) = 2 * (3 * k + 1) + 1 := by
        calc (3 ^ (j + 1) : ℤ) = 3 ^ j * 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j)); parley_side)
          _ = (2 * k + 1) * 3 := by parley_subst s1_3
          _ = 2 * (3 * k + 1) + 1 := by parley_ring
      -- 1.5. def:odd n := 3^(j + 1), from 1.4
      have s1_5 : Odd (3 ^ (j + 1) : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ (j + 1) : ℤ)))).mpr ⟨3 * k + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ (j + 1) : ℤ)))).mpr ⟨3 * k + 1, by parley_side⟩; parley_side)
      all_goals parley_side
  -- 2. instantiate j := n in line 1
  have s2 : Odd (3 ^ n : ℤ) := by first | exact (s1 n) | exact ((s1 n)).symm | simpa using (s1 n) | exact_mod_cast (s1 n) | (have h := (s1 n); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd
