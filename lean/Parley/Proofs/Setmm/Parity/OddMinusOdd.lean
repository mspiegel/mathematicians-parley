module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.OddMinusOdd

theorem odd_minus_odd (A : ℤ) (B : ℤ) (H3 : Odd A) (H4 : Odd B) :
    Even (A - B) := by
  -- 1. obtain k: def:odd n := A, from H3
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A))).mp (by parley_side)
  -- 2. obtain l: def:odd n := B, from H4
  obtain ⟨l, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := B))).mp (by parley_side)
  -- 3. algebra, from 1, 2
  have s3 : A - B = 2 * (k - l) := by linear_combination s1 + (-1) * s2
  -- 4. def:even n := A − B, from 3
  have s4 : Even (A - B) := ((Parley.Items.Stdlib.Divisibility.def_even (n := A - B))).mpr ⟨k - l, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Setmm.Parity.OddMinusOdd
