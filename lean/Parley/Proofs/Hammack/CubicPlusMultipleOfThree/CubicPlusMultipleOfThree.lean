module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/cubic-plus-multiple-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubicPlusMultipleOfThree.CubicPlusMultipleOfThree

theorem cubic_plus_multiple_of_three (n : ℕ) :
    (3 : ℤ) ∣ (n : ℤ) ^ 3 + 5 * (n : ℤ) + 6 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (3 : ℤ) ∣ (k : ℤ) ^ 3 + 5 * (k : ℤ) + 6 := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (3 : ℤ) ∣ (0 ^ 3 + 5 * 0 + 6 : ℤ) := by parley_arith
      all_goals parley_side
    | succ k hIH =>
      -- 1.2. mun:divides-self n := 3
      have s1_2 : (3 : ℤ) ∣ (3 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (3 : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (3 : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (3 : ℤ)))
      -- 1.3. mun:divides-multiple e := 3, a := 3, x := k² + k + 2, from 1.2
      have s1_3 : (3 : ℤ) ∣ 3 * ((k : ℤ) ^ 2 + (k : ℤ) + 2) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (3 : ℤ)) (x := (k : ℤ) ^ 2 + (k : ℤ) + 2) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (3 : ℤ)) (x := (k : ℤ) ^ 2 + (k : ℤ) + 2) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (3 : ℤ)) (x := (k : ℤ) ^ 2 + (k : ℤ) + 2) (by parley_side))
      -- 1.4. mun:divides-sum d := 3, a := k³ + 5k + 6, b := 3·(k² + k + 2), from IH, 1.3
      have s1_4 : (3 : ℤ) ∣ (k : ℤ) ^ 3 + 5 * (k : ℤ) + 6 + 3 * ((k : ℤ) ^ 2 + (k : ℤ) + 2) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := (k : ℤ) ^ 3 + 5 * (k : ℤ) + 6) (b := 3 * ((k : ℤ) ^ 2 + (k : ℤ) + 2)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := (k : ℤ) ^ 3 + 5 * (k : ℤ) + 6) (b := 3 * ((k : ℤ) ^ 2 + (k : ℤ) + 2)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := (k : ℤ) ^ 3 + 5 * (k : ℤ) + 6) (b := 3 * ((k : ℤ) ^ 2 + (k : ℤ) + 2)) (by parley_side) (by parley_side))
      -- 1.5. substitute
      have s1_5 : (3 : ℤ) ∣ ((k : ℤ) + 1) ^ 3 + 5 * ((k : ℤ) + 1) + 6 := by
        have c1 : (k : ℤ) ^ 3 + 5 * (k : ℤ) + 6 + 3 * ((k : ℤ) ^ 2 + (k : ℤ) + 2) = ((k : ℤ) + 1) ^ 3 + 5 * ((k : ℤ) + 1) + 6 := by parley_ring
        have row1 : (3 : ℤ) ∣ ((k : ℤ) + 1) ^ 3 + 5 * ((k : ℤ) + 1) + 6 := by parley_subst_at c1 s1_4
        exact row1
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (3 : ℤ) ∣ (n : ℤ) ^ 3 + 5 * (n : ℤ) + 6 := by first | exact (s1 n) | exact ((s1 n)).symm | simpa using (s1 n)
  all_goals parley_side

end Parley.Proofs.Hammack.CubicPlusMultipleOfThree.CubicPlusMultipleOfThree
