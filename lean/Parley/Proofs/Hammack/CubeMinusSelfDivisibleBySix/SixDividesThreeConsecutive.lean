module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/cube-minus-self-divisible-by-six.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive

theorem six_divides_three_consecutive (k : ℕ) :
    (6 : ℤ) ∣ 3 * (k : ℤ) * ((k : ℤ) + 1) := by
  -- 1. mun:even-or-odd n := k
  have s1 : Even (k : ℤ) ∨ Odd (k : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (k : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (k : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (k : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (k : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (k : ℤ))); parley_side)
  -- 2. cases, from 1
  have s2 : (6 : ℤ) ∣ 3 * (k : ℤ) * ((k : ℤ) + 1) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain m: def:even n := k, from C1
      obtain ⟨m, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (k : ℤ)))).mp (by parley_side)
      -- 2.2. calculation
      have s2_2 : 3 * (k : ℤ) * ((k : ℤ) + 1) = 6 * (m * (2 * m + 1)) := by
        calc 3 * (k : ℤ) * ((k : ℤ) + 1) = 3 * (2 * m) * (2 * m + 1) := by parley_subst s2_1
          _ = 6 * (m * (2 * m + 1)) := by parley_ring
      -- 2.3. def:divides d := 6, n := 3·k·(k + 1), from 2.2
      have s2_3 : (6 : ℤ) ∣ 3 * (k : ℤ) * ((k : ℤ) + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (6 : ℤ)) (n := 3 * (k : ℤ) * ((k : ℤ) + 1)))).mpr ⟨m * (2 * m + 1), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (6 : ℤ)) (n := 3 * (k : ℤ) * ((k : ℤ) + 1)))).mpr ⟨m * (2 * m + 1), by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      -- 2.4. obtain m: def:odd n := k, from C2
      obtain ⟨m, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (k : ℤ)))).mp (by parley_side)
      -- 2.5. calculation
      have s2_5 : 3 * (k : ℤ) * ((k : ℤ) + 1) = 6 * ((2 * m + 1) * (m + 1)) := by
        calc 3 * (k : ℤ) * ((k : ℤ) + 1) = 3 * (2 * m + 1) * (2 * m + 1 + 1) := by parley_subst s2_4
          _ = 6 * ((2 * m + 1) * (m + 1)) := by parley_ring
      -- 2.6. def:divides d := 6, n := 3·k·(k + 1), from 2.5
      have s2_6 : (6 : ℤ) ∣ 3 * (k : ℤ) * ((k : ℤ) + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (6 : ℤ)) (n := 3 * (k : ℤ) * ((k : ℤ) + 1)))).mpr ⟨(2 * m + 1) * (m + 1), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (6 : ℤ)) (n := 3 * (k : ℤ) * ((k : ℤ) + 1)))).mpr ⟨(2 * m + 1) * (m + 1), by parley_side⟩; parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive
