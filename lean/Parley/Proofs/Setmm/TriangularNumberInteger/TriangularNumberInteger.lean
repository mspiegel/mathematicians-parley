module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/triangular-number-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger

theorem triangular_number_integer (n : ℤ) :
    (∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  have s2 : ∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by
    rcases s1 with C1 | C2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp (by parley_side)
      -- 2.2. algebra, from 2.1
      have s2_2 : (n : ℚ) * ((n : ℚ) + 1) / 2 = (k : ℚ) * (2 * (k : ℚ) + 1) := by linear_combination ((k : ℚ) + (1 / 2 : ℚ) * (n : ℚ) + (1 / 2 : ℚ)) * s2_1
      -- 2.3. membership, from 2.2
      have s2_3 : ∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by parley_side
      parley_side
    · skip
      -- 2.4. obtain k: def:odd, from C2
      obtain ⟨k, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
      -- 2.5. algebra, from 2.4
      have s2_5 : (n : ℚ) * ((n : ℚ) + 1) / 2 = (2 * (k : ℚ) + 1) * ((k : ℚ) + 1) := by linear_combination ((k : ℚ) + (1 / 2 : ℚ) * (n : ℚ) + 1) * s2_4
      -- 2.6. membership, from 2.5
      have s2_6 : ∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by parley_side
      parley_side
  parley_side

end Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger
