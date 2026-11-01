module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from proofs/hammack/square-mod-four.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareModFour.SquareModFour

theorem square_mod_four (n : ℤ) :
    ((4 : ℤ) ∣ n ^ 2 ∨ (4 : ℤ) ∣ n ^ 2 - 1) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  have s2 : (4 : ℤ) ∣ n ^ 2 ∨ (4 : ℤ) ∣ n ^ 2 - 1 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp (by parley_side)
      -- 2.2. algebra, from 2.1
      have s2_2 : n ^ 2 = 4 * k ^ 2 := by linear_combination (2 * k + n) * s2_1
      -- 2.3. def:divides d := 4, n := n², from 2.2
      have s2_3 : (4 : ℤ) ∣ n ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := n ^ 2))).mpr ⟨k ^ 2, by parley_side⟩
      -- 2.4. mun:or-left, from 2.3
      have s2_4 : (4 : ℤ) ∣ n ^ 2 ∨ (4 : ℤ) ∣ n ^ 2 - 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) (by parley_side))
      all_goals parley_side
    · skip
      -- 2.5. obtain k: def:odd, from C2
      obtain ⟨k, s2_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
      -- 2.6. algebra, from 2.5
      have s2_6 : n ^ 2 - 1 = 4 * (k ^ 2 + k) := by linear_combination (2 * k + n + 1) * s2_5
      -- 2.7. def:divides d := 4, n := n² − 1, from 2.6
      have s2_7 : (4 : ℤ) ∣ n ^ 2 - 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨k ^ 2 + k, by parley_side⟩
      -- 2.8. mun:or-right, from 2.7
      have s2_8 : (4 : ℤ) ∣ n ^ 2 ∨ (4 : ℤ) ∣ n ^ 2 - 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) (by parley_side))
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SquareModFour.SquareModFour
