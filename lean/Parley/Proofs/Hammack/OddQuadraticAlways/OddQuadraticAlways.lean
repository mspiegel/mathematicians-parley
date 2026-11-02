module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/odd-quadratic-always.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddQuadraticAlways.OddQuadraticAlways

theorem odd_quadratic_always (n : ℤ) :
    Odd (5 * n ^ 2 + 3 * n + 7) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  have s2 : Odd (5 * n ^ 2 + 3 * n + 7) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp (by parley_side)
      -- 2.2. calculation
      have s2_2 : 5 * n ^ 2 + 3 * n + 7 = 2 * (10 * k ^ 2 + 3 * k + 3) + 1 := by
        calc 5 * n ^ 2 + 3 * n + 7 = 5 * (2 * k) ^ 2 + 3 * (2 * k) + 7 := by parley_subst s2_1
          _ = 2 * (10 * k ^ 2 + 3 * k + 3) + 1 := by parley_ring
      -- 2.3. def:odd n := 5n² + 3n + 7, from 2.2
      have s2_3 : Odd (5 * n ^ 2 + 3 * n + 7) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := 5 * n ^ 2 + 3 * n + 7))).mpr ⟨10 * k ^ 2 + 3 * k + 3, by parley_side⟩
      all_goals parley_side
    · skip
      -- 2.4. obtain k: def:odd, from C2
      obtain ⟨k, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
      -- 2.5. calculation
      have s2_5 : 5 * n ^ 2 + 3 * n + 7 = 2 * (10 * k ^ 2 + 13 * k + 7) + 1 := by
        calc 5 * n ^ 2 + 3 * n + 7 = 5 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 7 := by parley_subst s2_4
          _ = 2 * (10 * k ^ 2 + 13 * k + 7) + 1 := by parley_ring
      -- 2.6. def:odd n := 5n² + 3n + 7, from 2.5
      have s2_6 : Odd (5 * n ^ 2 + 3 * n + 7) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := 5 * n ^ 2 + 3 * n + 7))).mpr ⟨10 * k ^ 2 + 13 * k + 7, by parley_side⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.OddQuadraticAlways.OddQuadraticAlways
