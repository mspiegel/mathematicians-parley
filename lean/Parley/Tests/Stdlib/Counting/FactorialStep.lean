module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialStep

theorem factorial_step (n : ℕ) :
    (Nat.factorial (n + 1) : ℤ) = (Nat.factorial n : ℤ) * ((n : ℤ) + 1) := by
  -- 1. def:factorial
  have s1 : (Nat.factorial (n + 1) : ℤ) = (Nat.factorial n : ℤ) * ((n : ℤ) + 1) := by linear_combination (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n))
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.FactorialStep
