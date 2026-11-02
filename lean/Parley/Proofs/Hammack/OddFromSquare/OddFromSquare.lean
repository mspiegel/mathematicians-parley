module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/odd-from-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddFromSquare.OddFromSquare

theorem odd_from_square (a : ℤ) (hH2 : ¬ (4 : ℤ) ∣ a ^ 2) :
    Odd a := by
  -- 1. mun:even-or-odd
  have s1 : Even a ∨ Odd a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)); parley_side)
  -- 2. cases, from 1
  have s2 : Odd a := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
      -- 2.2. algebra, from 2.1
      have s2_2 : a ^ 2 = 4 * k ^ 2 := by linear_combination (norm := parley_norm) (a + 2 * k) * s2_1
      -- 2.3. def:divides d := 4, n := a², from 2.2
      have s2_3 : (4 : ℤ) ∣ a ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := a ^ 2))).mpr ⟨k ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := a ^ 2))).mpr ⟨k ^ 2, by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.OddFromSquare.OddFromSquare
