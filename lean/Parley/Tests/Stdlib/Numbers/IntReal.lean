module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.IntReal

theorem int_real (m : ℤ) :
    True := by
  -- 1. mun:numbers-int-real
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.IntReal
