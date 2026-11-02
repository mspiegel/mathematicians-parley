module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/five-power-minus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FivePowerMinusOne.FivePowerMinusOne

theorem five_power_minus_one (n : ℕ) :
    (3 : ℤ) ∣ (5 ^ (2 * n) - 1 : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, (3 : ℤ) ∣ (5 ^ (2 * m) - 1 : ℤ) := by
    intro m
    induction m with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (5 ^ (2 * 0) - 1 : ℤ) = 3 * 0 := by parley_arith
      -- 1.2. def:divides d := 3, n := 5^(2·0) − 1, from 1.1
      have s1_2 : (3 : ℤ) ∣ (5 ^ (2 * 0) - 1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (5 ^ (2 * 0) - 1 : ℤ)))).mpr ⟨(0 : ℤ), by parley_side⟩
      all_goals parley_side
    | succ m hIH =>
      -- 1.3. algebra
      have s1_3 : 2 * ((m : ℤ) + 1) = 2 * (m : ℤ) + 2 := by parley_ring
      -- 1.4. calculation
      have s1_4 : (5 ^ (2 * (m + 1)) : ℤ) = 5 ^ (2 * m) * 5 ^ 2 := by
        calc (5 ^ (2 * (m + 1)) : ℤ) = 5 ^ (2 * m + 2) := by parley_subst s1_3
          _ = 5 ^ (2 * m) * 5 ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (n := 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (n := 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (n := 2)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (n := 2))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (n := 2)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (n := 2)); qify; linear_combination (norm := parley_norm) h)
      -- 1.5. mun:divides-multiple e := 3, a := 5^(2m) − 1, x := 25, from IH
      have s1_5 : (3 : ℤ) ∣ ((5 ^ (2 * m) - 1) * 25 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (5 ^ (2 * m) - 1 : ℤ)) (x := (25 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (5 ^ (2 * m) - 1 : ℤ)) (x := (25 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (5 ^ (2 * m) - 1 : ℤ)) (x := (25 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (5 ^ (2 * m) - 1 : ℤ)) (x := (25 : ℤ)) (by parley_side))
      -- 1.6. def:divides d := 3, n := 24
      have r37_1 : (24 : ℤ) = 3 * 8 := by parley_arith
      have s1_6 : (3 : ℤ) ∣ (24 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (24 : ℤ)))).mpr ⟨(8 : ℤ), by parley_side⟩
      -- 1.7. mun:divides-sum d := 3, a := (5^(2m) − 1)·25, b := 24, from 1.5, 1.6
      have s1_7 : (3 : ℤ) ∣ ((5 ^ (2 * m) - 1) * 25 + 24 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := ((5 ^ (2 * m) - 1) * 25 : ℤ)) (b := (24 : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := ((5 ^ (2 * m) - 1) * 25 : ℤ)) (b := (24 : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := ((5 ^ (2 * m) - 1) * 25 : ℤ)) (b := (24 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := ((5 ^ (2 * m) - 1) * 25 : ℤ)) (b := (24 : ℤ)) (by parley_side) (by parley_side))
      -- 1.8. substitute
      have s1_8 : (3 : ℤ) ∣ (5 ^ (2 * (m + 1)) - 1 : ℤ) := by
        have c1 : ((5 ^ (2 * m) - 1) * 25 + 24 : ℤ) = 5 ^ (2 * (m + 1)) - 1 := by linear_combination (norm := parley_norm) (-1) * s1_4
        have row1 : (3 : ℤ) ∣ (5 ^ (2 * (m + 1)) - 1 : ℤ) := by parley_subst_at c1 s1_7
        exact row1
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : (3 : ℤ) ∣ (5 ^ (2 * n) - 1 : ℤ) := by first | exact (s1 n) | exact ((s1 n)).symm | simpa using (s1 n) | exact_mod_cast (s1 n)
  all_goals parley_side

end Parley.Proofs.Hammack.FivePowerMinusOne.FivePowerMinusOne
