module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialAtMost

theorem factorial_at_most (a : ℕ) (b : ℕ) (hH3 : (a : ℤ) ≤ (b : ℤ)) :
    (Parley.Library.factorial (a : ℤ) : ℤ) ≤ (Parley.Library.factorial (b : ℤ) : ℤ) := by
  -- 1. mun:counting-factorial-at-most m := a, n := b, from H3
  have s1 : (Parley.Library.factorial (a : ℤ) : ℤ) ≤ (Parley.Library.factorial (b : ℤ) : ℤ) := by first | linarith [(Parley.Items.Stdlib.Counting.mun_factorial_at_most (m := a) (n := b) (by parley_side))] | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_at_most (m := a) (n := b) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_at_most (m := a) (n := b) (by parley_side))
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.FactorialAtMost
