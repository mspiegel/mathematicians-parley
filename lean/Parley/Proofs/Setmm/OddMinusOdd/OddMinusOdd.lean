module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/odd-minus-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddMinusOdd.OddMinusOdd

theorem odd_minus_odd (A : ℤ) (B : ℤ) (H3 : Odd A) (H4 : Odd B) :
    (2 : ℤ) ∣ A - B := by
  -- 1. obtain a: def:odd n := A, from H3
  obtain ⟨a, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A))).mp (by parley_side)
  -- 2. obtain b: def:odd n := B, from H4
  obtain ⟨b, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := B))).mp (by parley_side)
  -- 3. algebra, from 1, 2
  have s3 : A - B = 2 * (a - b) := by linear_combination s1 + (-1) * s2
  -- 4. def:divides d := 2, n := A − B, from 3
  have s4 : (2 : ℤ) ∣ A - B := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := A - B))).mpr ⟨a - b, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Setmm.OddMinusOdd.OddMinusOdd
