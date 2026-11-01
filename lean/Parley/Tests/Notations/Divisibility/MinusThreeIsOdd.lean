module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.MinusThreeIsOdd

theorem minus_three_is_odd :
    Odd (-3 : ℤ) := by
  -- 1. arithmetic
  have s1 : (-3 : ℤ) = 2 * -2 + 1 := by parley_arith
  -- 2. def:odd n := −3, from 1
  have s2 : Odd (-3 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (-3 : ℤ)))).mpr ⟨(-2 : ℤ), by parley_side⟩
  all_goals parley_side

end Parley.Tests.Notations.Divisibility.MinusThreeIsOdd
