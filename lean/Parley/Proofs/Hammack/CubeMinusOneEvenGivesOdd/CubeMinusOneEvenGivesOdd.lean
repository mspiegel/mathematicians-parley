module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/cube-minus-one-even-gives-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeMinusOneEvenGivesOdd.CubeMinusOneEvenGivesOdd

theorem cube_minus_one_even_gives_odd (x : ℤ) (hH2 : Even (x ^ 3 - 1)) :
    Odd x := by
  -- 1. mun:even-or-odd n := x
  have s1 : Even x ∨ Odd x := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x)); parley_side)
  -- 2. cases, from 1
  have s2 : Odd x := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := x))).mp (by parley_side)
      -- 2.2. calculation
      have s2_2 : x ^ 3 - 1 = 2 * (4 * k ^ 3 - 1) + 1 := by
        calc x ^ 3 - 1 = (2 * k) ^ 3 - 1 := by parley_subst s2_1
          _ = 2 * (4 * k ^ 3 - 1) + 1 := by parley_ring
      -- 2.3. def:odd n := x³ − 1, from 2.2
      have s2_3 : Odd (x ^ 3 - 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := x ^ 3 - 1))).mpr ⟨4 * k ^ 3 - 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x ^ 3 - 1))).mpr ⟨4 * k ^ 3 - 1, by parley_side⟩; parley_side)
      -- 2.4. mun:not-both n := x³ − 1, from H2
      have s2_4 : ¬ Odd (x ^ 3 - 1) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 3 - 1) hH2) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 3 - 1) hH2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 3 - 1) hH2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 3 - 1) hH2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 3 - 1) hH2); parley_side)
      all_goals parley_side
    · skip
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.CubeMinusOneEvenGivesOdd.CubeMinusOneEvenGivesOdd
