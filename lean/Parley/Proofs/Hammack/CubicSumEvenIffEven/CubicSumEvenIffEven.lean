module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/cubic-sum-even-iff-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubicSumEvenIffEven.CubicSumEvenIffEven

theorem cubic_sum_even_iff_even (a : ℤ) :
    (Even (a ^ 3 + a ^ 2 + a) ↔ Even a) := by
  -- the theorem. both directions
  have sThm : Even (a ^ 3 + a ^ 2 + a) ↔ Even a := by
    constructor
    · skip
      intro hD1
      -- 1. mun:even-or-odd n := a
      have s1 : Even a ∨ Odd a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)); parley_side)
      -- 2. cases, from 1
      have s2 : Even a := by
        rcases s1 with hC1 | hC2
        · skip
          all_goals parley_side
        · skip
          -- 2.1. obtain k: def:odd, from C2
          obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp (by parley_side)
          -- 2.2. algebra, from 2.1
          have s2_2 : a ^ 3 + a ^ 2 + a = 2 * (4 * k ^ 3 + 8 * k ^ 2 + 6 * k + 1) + 1 := by linear_combination (norm := parley_norm) (2 * a * k + a ^ 2 + 4 * k ^ 2 + 2 * a + 6 * k + 3) * s2_1
          -- 2.3. def:odd n := a³ + a² + a, from 2.2
          have s2_3 : Odd (a ^ 3 + a ^ 2 + a) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := a ^ 3 + a ^ 2 + a))).mpr ⟨4 * k ^ 3 + 8 * k ^ 2 + 6 * k + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a ^ 3 + a ^ 2 + a))).mpr ⟨4 * k ^ 3 + 8 * k ^ 2 + 6 * k + 1, by parley_side⟩; parley_side)
          -- 2.4. mun:not-both n := a³ + a² + a, from D1
          have s2_4 : ¬ Odd (a ^ 3 + a ^ 2 + a) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 3 + a ^ 2 + a) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 3 + a ^ 2 + a) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 3 + a ^ 2 + a) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 3 + a ^ 2 + a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 3 + a ^ 2 + a) (by parley_side)); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 3. obtain k: def:even, from D2
      obtain ⟨k, s3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
      -- 4. algebra, from 3
      have s4 : a ^ 3 + a ^ 2 + a = 2 * (4 * k ^ 3 + 2 * k ^ 2 + k) := by linear_combination (norm := parley_norm) (2 * a * k + a ^ 2 + 4 * k ^ 2 + a + 2 * k + 1) * s3
      -- 5. def:even n := a³ + a² + a, from 4
      have s5 : Even (a ^ 3 + a ^ 2 + a) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 3 + a ^ 2 + a))).mpr ⟨4 * k ^ 3 + 2 * k ^ 2 + k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 3 + a ^ 2 + a))).mpr ⟨4 * k ^ 3 + 2 * k ^ 2 + k, by parley_side⟩; parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.CubicSumEvenIffEven.CubicSumEvenIffEven
