module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.OddPlusEven

theorem odd_plus_even (a : ℤ) (hH2 : Odd a) (b : ℤ) (hH4 : Even b) :
    Odd (a + b) := by
  -- 1. mun:divisibility-odd-plus-even, from H2, H4
  have s1 : Odd (a + b) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_odd_plus_even (a := a) hH2 (b := b) hH4) | exact ((Parley.Items.Stdlib.Divisibility.mun_odd_plus_even (a := a) hH2 (b := b) hH4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_odd_plus_even (a := a) hH2 (b := b) hH4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_odd_plus_even (a := a) hH2 (b := b) hH4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_odd_plus_even (a := a) hH2 (b := b) hH4); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.OddPlusEven
