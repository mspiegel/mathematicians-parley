module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/divisible-by-nine.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DivisibleByNine.DivisibleByNine

theorem divisible_by_nine (n : ℕ) :
    (9 : ℤ) ∣ (4 ^ (3 * n) + 8 : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, (9 : ℤ) ∣ (4 ^ (3 * m) + 8 : ℤ) := by
    intro m
    induction m with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (4 ^ (3 * 0) + 8 : ℤ) = 9 * 1 := by parley_arith
      -- 1.2. def:divides d := 9, n := 4^(3·0) + 8, from 1.1
      have s1_2 : (9 : ℤ) ∣ (4 ^ (3 * 0) + 8 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (9 : ℤ)) (n := (4 ^ (3 * 0) + 8 : ℤ)))).mpr ⟨(1 : ℤ), by parley_side⟩
      all_goals parley_side
    | succ m hIH =>
      -- 1.3. algebra
      have s1_3 : 3 * ((m : ℤ) + 1) = 3 * (m : ℤ) + 3 := by parley_ring
      -- 1.4. calculation
      have s1_4 : (4 ^ (3 * (m + 1)) : ℤ) = 4 ^ (3 * m) * 4 ^ 3 := by
        calc (4 ^ (3 * (m + 1)) : ℤ) = 4 ^ (3 * m + 3) := by parley_subst s1_3
          _ = 4 ^ (3 * m) * 4 ^ 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (4 : ℤ)) (m := 3 * m) (n := 3)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (4 : ℤ)) (m := 3 * m) (n := 3)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (4 : ℤ)) (m := 3 * m) (n := 3)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (4 : ℤ)) (m := 3 * m) (n := 3))).symm
      -- 1.5. mun:divides-multiple e := 9, a := 4^(3m) + 8, x := 64, from IH
      have s1_5 : (9 : ℤ) ∣ ((4 ^ (3 * m) + 8) * 64 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (9 : ℤ)) (a := (4 ^ (3 * m) + 8 : ℤ)) (x := (64 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (9 : ℤ)) (a := (4 ^ (3 * m) + 8 : ℤ)) (x := (64 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (9 : ℤ)) (a := (4 ^ (3 * m) + 8 : ℤ)) (x := (64 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (9 : ℤ)) (a := (4 ^ (3 * m) + 8 : ℤ)) (x := (64 : ℤ)) (by parley_side))
      -- 1.6. def:divides d := 9, n := 504
      have r37_1 : (504 : ℤ) = 9 * 56 := by parley_arith
      have s1_6 : (9 : ℤ) ∣ (504 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (9 : ℤ)) (n := (504 : ℤ)))).mpr ⟨(56 : ℤ), by parley_side⟩
      -- 1.7. mun:divides-difference d := 9, a := (4^(3m) + 8)·64, b := 504, from 1.5, 1.6
      have s1_7 : (9 : ℤ) ∣ ((4 ^ (3 * m) + 8) * 64 - 504 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (9 : ℤ)) (a := ((4 ^ (3 * m) + 8) * 64 : ℤ)) (b := (504 : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (9 : ℤ)) (a := ((4 ^ (3 * m) + 8) * 64 : ℤ)) (b := (504 : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (9 : ℤ)) (a := ((4 ^ (3 * m) + 8) * 64 : ℤ)) (b := (504 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (9 : ℤ)) (a := ((4 ^ (3 * m) + 8) * 64 : ℤ)) (b := (504 : ℤ)) (by parley_side) (by parley_side))
      -- 1.8. substitute
      have s1_8 : (9 : ℤ) ∣ (4 ^ (3 * (m + 1)) + 8 : ℤ) := by
        have c1 : ((4 ^ (3 * m) + 8) * 64 - 504 : ℤ) = 4 ^ (3 * (m + 1)) + 8 := by linear_combination (norm := parley_norm) (-1) * s1_4
        have row1 : (9 : ℤ) ∣ (4 ^ (3 * (m + 1)) + 8 : ℤ) := by parley_subst_at c1 s1_7
        exact row1
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : (9 : ℤ) ∣ (4 ^ (3 * n) + 8 : ℤ) := by first | exact (s1 n) | exact ((s1 n)).symm | simpa using (s1 n) | exact_mod_cast (s1 n)
  all_goals parley_side

end Parley.Proofs.Hammack.DivisibleByNine.DivisibleByNine
