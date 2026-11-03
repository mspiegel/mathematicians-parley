module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.FloorOfSevenHalves

theorem floor_of_seven_halves :
    ⌊(7 / 2 : ℚ)⌋ = 3 := by
  -- 1. mun:floor-between x := 7/2, k := 3
  have r133_1 : (3 : ℚ) ≤ 7 / 2 := by parley_arith
  have r133_2 : (7 / 2 : ℚ) < 3 + 1 := by parley_arith
  have s1 : ⌊(7 / 2 : ℚ)⌋ = 3 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (7 / 2 : ℚ)) (k := (3 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (7 / 2 : ℚ)) (k := (3 : ℤ)))).mpr (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Primes.FloorOfSevenHalves
