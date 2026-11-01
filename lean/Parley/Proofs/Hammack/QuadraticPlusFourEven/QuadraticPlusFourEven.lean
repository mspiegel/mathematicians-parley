module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/quadratic-plus-four-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.QuadraticPlusFourEven.QuadraticPlusFourEven

theorem quadratic_plus_four_even (n : ℤ) :
    Even (n ^ 2 + 3 * n + 4) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  have s2 : Even (n ^ 2 + 3 * n + 4) := by
    rcases s1 with C1 | C2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp (by parley_side)
      -- 2.2. calculation
      have s2_2 : n ^ 2 + 3 * n + 4 = 2 * (2 * k ^ 2 + 3 * k + 2) := by
        calc n ^ 2 + 3 * n + 4 = (2 * k) ^ 2 + 3 * (2 * k) + 4 := by parley_subst s2_1
          _ = 2 * (2 * k ^ 2 + 3 * k + 2) := by ring
      -- 2.3. def:even n := n² + 3n + 4, from 2.2
      have s2_3 : Even (n ^ 2 + 3 * n + 4) := ((Parley.Items.Stdlib.Divisibility.def_even (n := n ^ 2 + 3 * n + 4))).mpr ⟨2 * k ^ 2 + 3 * k + 2, by parley_side⟩
      all_goals parley_side
    · skip
      -- 2.4. obtain k: def:odd, from C2
      obtain ⟨k, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
      -- 2.5. calculation
      have s2_5 : n ^ 2 + 3 * n + 4 = 2 * (2 * k ^ 2 + 5 * k + 4) := by
        calc n ^ 2 + 3 * n + 4 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 4 := by parley_subst s2_4
          _ = 2 * (2 * k ^ 2 + 5 * k + 4) := by ring
      -- 2.6. def:even n := n² + 3n + 4, from 2.5
      have s2_6 : Even (n ^ 2 + 3 * n + 4) := ((Parley.Items.Stdlib.Divisibility.def_even (n := n ^ 2 + 3 * n + 4))).mpr ⟨2 * k ^ 2 + 5 * k + 4, by parley_side⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.QuadraticPlusFourEven.QuadraticPlusFourEven
