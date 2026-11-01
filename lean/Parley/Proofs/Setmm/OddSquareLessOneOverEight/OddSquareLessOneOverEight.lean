module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library
public import Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger

/-! Written from proofs/setmm/odd-square-less-one-over-eight.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddSquareLessOneOverEight.OddSquareLessOneOverEight

theorem odd_square_less_one_over_eight (n : ℤ) (H2 : Odd n) :
    (∃ m : ℤ, (m : ℚ) = ((n : ℚ) ^ 2 - 1) / 8) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. algebra, from 1
  have s2 : ((n : ℚ) ^ 2 - 1) / 8 = (k : ℚ) * ((k : ℚ) + 1) / 2 := by linear_combination ((1 / 4 : ℚ) * (k : ℚ) + (1 / 8 : ℚ) * (n : ℚ) + (1 / 8 : ℚ)) * s1
  -- 3. thm:triangular-number-integer n := k
  have s3 : ∃ m : ℤ, (m : ℚ) = (k : ℚ) * ((k : ℚ) + 1) / 2 := by simpa using (Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger.triangular_number_integer (n := k))
  -- 4. membership, from 2, 3
  have s4 : ∃ m : ℤ, (m : ℚ) = ((n : ℚ) ^ 2 - 1) / 8 := by parley_side
  parley_side

end Parley.Proofs.Setmm.OddSquareLessOneOverEight.OddSquareLessOneOverEight
