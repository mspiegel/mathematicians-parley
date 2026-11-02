module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/eight-divides-odd-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.EightDividesOddSquare.EightDividesOddSquare

theorem eight_divides_odd_square (n : ℤ) (hH2 : Odd n) :
    (8 : ℤ) ∣ n ^ 2 - 1 := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. calculation
  have s2 : n ^ 2 - 1 = 4 * (k * (k + 1)) := by
    calc n ^ 2 - 1 = (2 * k + 1) ^ 2 - 1 := by parley_subst s1
      _ = 4 * (k * (k + 1)) := by parley_ring
  -- 3. mun:even-or-odd n := k
  have s3 : Even k ∨ Odd k := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k)); parley_side)
  -- 4. cases, from 3
  have s4 : (8 : ℤ) ∣ n ^ 2 - 1 := by
    rcases s3 with hC1 | hC2
    · skip
      -- 4.1. obtain j: def:even n := k, from C1
      obtain ⟨j, s4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := k))).mp (by parley_side)
      -- 4.2. substitute k = 2j (line 4.1) into line 2
      have s4_2 : n ^ 2 - 1 = 4 * (2 * j * (2 * j + 1)) := by parley_subst_at s4_1 s2
      -- 4.3. calculation
      have s4_3 : n ^ 2 - 1 = 8 * (j * (2 * j + 1)) := by
        calc n ^ 2 - 1 = 4 * (2 * j * (2 * j + 1)) := by parley_side
          _ = 8 * (j * (2 * j + 1)) := by parley_ring
      -- 4.4. def:divides d := 8, n := n² − 1, from 4.3
      have s4_4 : (8 : ℤ) ∣ n ^ 2 - 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (8 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨j * (2 * j + 1), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (8 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨j * (2 * j + 1), by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      -- 4.5. obtain j: def:odd n := k, from C2
      obtain ⟨j, s4_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := k))).mp (by parley_side)
      -- 4.6. substitute k = 2j + 1 (line 4.5) into line 2
      have s4_6 : n ^ 2 - 1 = 4 * ((2 * j + 1) * (2 * j + 1 + 1)) := by parley_subst_at s4_5 s2
      -- 4.7. calculation
      have s4_7 : n ^ 2 - 1 = 8 * ((2 * j + 1) * (j + 1)) := by
        calc n ^ 2 - 1 = 4 * ((2 * j + 1) * (2 * j + 1 + 1)) := by parley_side
          _ = 8 * ((2 * j + 1) * (j + 1)) := by parley_ring
      -- 4.8. def:divides d := 8, n := n² − 1, from 4.7
      have s4_8 : (8 : ℤ) ∣ n ^ 2 - 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (8 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨(2 * j + 1) * (j + 1), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (8 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨(2 * j + 1) * (j + 1), by parley_side⟩; parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.EightDividesOddSquare.EightDividesOddSquare
