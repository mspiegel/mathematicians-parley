module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.FloorOfMinusHalf

theorem floor_of_minus_half :
    ⌊(-(1 / 2) : ℚ)⌋ = -1 := by
  -- 1. mun:floor-between x := −1/2, k := −1
  have r110_1 : (-1 : ℚ) ≤ -(1 / 2) := by parley_arith
  have r110_2 : (-(1 / 2) : ℚ) < -1 + 1 := by parley_arith
  have s1 : ⌊(-(1 / 2) : ℚ)⌋ = -1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (-(1 / 2) : ℚ)) (k := (-1 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (-(1 / 2) : ℚ)) (k := (-1 : ℤ)))).mpr (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Primes.FloorOfMinusHalf
