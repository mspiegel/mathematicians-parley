module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.OddMinusOdd

theorem odd_minus_odd (a : ℤ) (hH2 : Odd a) (b : ℤ) (hH4 : Odd b) :
    Even (a - b) := by
  -- 1. mun:divisibility-odd-minus-odd, from H2, H4
  have s1 : Even (a - b) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_odd_minus_odd (a := a) hH2 (b := b) hH4) | exact ((Parley.Items.Stdlib.Divisibility.mun_odd_minus_odd (a := a) hH2 (b := b) hH4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_odd_minus_odd (a := a) hH2 (b := b) hH4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_odd_minus_odd (a := a) hH2 (b := b) hH4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_odd_minus_odd (a := a) hH2 (b := b) hH4); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.OddMinusOdd
