module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.EvenPlusOdd

theorem even_plus_odd (A : ℤ) (B : ℤ) (hH3 : Even A) (hH4 : Odd B) :
    Odd (A + B) := by
  -- 1. obtain k: def:even n := A, from H3
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := A))).mp (by parley_side)
  -- 2. obtain l: def:odd n := B, from H4
  obtain ⟨l, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := B))).mp (by parley_side)
  -- 3. algebra, from 1, 2
  have s3 : A + B = 2 * (k + l) + 1 := by linear_combination s1 + s2
  -- 4. def:odd n := A + B, from 3
  have s4 : Odd (A + B) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A + B))).mpr ⟨k + l, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Setmm.Parity.EvenPlusOdd
