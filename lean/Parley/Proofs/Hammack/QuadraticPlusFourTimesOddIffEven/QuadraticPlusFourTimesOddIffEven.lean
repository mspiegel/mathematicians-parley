module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/quadratic-plus-four-times-odd-iff-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.QuadraticPlusFourTimesOddIffEven.QuadraticPlusFourTimesOddIffEven

theorem quadratic_plus_four_times_odd_iff_even (a : ℤ) :
    (Odd (a ^ 2 + 4 * a + 5) ↔ Even a) := by
  -- the theorem. both directions
  have sThm : Odd (a ^ 2 + 4 * a + 5) ↔ Even a := by
    constructor
    · skip
      intro hD1
      -- 1. mun:even-or-odd n := a
      have s1 : Even a ∨ Odd a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))
      -- 2. cases, from 1
      have s2 : Even a := by
        rcases s1 with hC1 | hC2
        · skip
          all_goals parley_side
        · skip
          -- 2.1. obtain k: def:odd, from C2
          obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp (by parley_side)
          -- 2.2. algebra, from 2.1
          have s2_2 : a ^ 2 + 4 * a + 5 = 2 * (2 * k ^ 2 + 6 * k + 5) := by linear_combination (norm := parley_norm) (a + 2 * k + 5) * s2_1
          -- 2.3. def:even n := a² + 4a + 5, from 2.2
          have s2_3 : Even (a ^ 2 + 4 * a + 5) := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2 + 4 * a + 5))).mpr ⟨2 * k ^ 2 + 6 * k + 5, by parley_side⟩
          -- 2.4. mun:not-both n := a² + 4a + 5, from 2.3
          have s2_4 : ¬ Odd (a ^ 2 + 4 * a + 5) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 + 4 * a + 5) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 + 4 * a + 5) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 + 4 * a + 5) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 + 4 * a + 5) (by parley_side))
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 3. obtain k: def:even, from D2
      obtain ⟨k, s3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
      -- 4. algebra, from 3
      have s4 : a ^ 2 + 4 * a + 5 = 2 * (2 * k ^ 2 + 4 * k + 2) + 1 := by linear_combination (norm := parley_norm) (a + 2 * k + 4) * s3
      -- 5. def:odd n := a² + 4a + 5, from 4
      have s5 : Odd (a ^ 2 + 4 * a + 5) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a ^ 2 + 4 * a + 5))).mpr ⟨2 * k ^ 2 + 4 * k + 2, by parley_side⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.QuadraticPlusFourTimesOddIffEven.QuadraticPlusFourTimesOddIffEven
