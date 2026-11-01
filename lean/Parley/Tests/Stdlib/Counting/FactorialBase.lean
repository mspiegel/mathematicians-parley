module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialBase

theorem factorial_base :
    (Nat.factorial 1 : ℤ) = 1 := by
  -- 1. def:factorial
  have s1 : (Nat.factorial 1 : ℤ) = 1 := by linear_combination Parley.Items.Stdlib.Counting.def_factorial_2
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.FactorialBase
