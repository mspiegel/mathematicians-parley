module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/odd-from-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddFromSquare.OddFromSquare

theorem odd_from_square (a : ℤ) (H2 : ¬ (4 : ℤ) ∣ a ^ 2) :
    Odd a := by
  -- 1. mun:even-or-odd
  have s1 : Even a ∨ Odd a := by simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))
  -- 2. cases, from 1
  have s2 : Odd a := by
    rcases s1 with C1 | C2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
      -- 2.2. algebra, from 2.1
      have s2_2 : a ^ 2 = 4 * k ^ 2 := by linear_combination (a + 2 * k) * s2_1
      -- 2.3. def:divides d := 4, n := a², from 2.2
      have s2_3 : (4 : ℤ) ∣ a ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := a ^ 2))).mpr ⟨k ^ 2, by parley_side⟩
      parley_side
    · skip
      parley_side
  parley_side

end Parley.Proofs.Hammack.OddFromSquare.OddFromSquare
