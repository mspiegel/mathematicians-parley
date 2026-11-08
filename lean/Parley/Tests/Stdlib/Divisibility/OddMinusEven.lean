module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.OddMinusEven

theorem odd_minus_even (a : ℤ) (hH2 : Odd a) (b : ℤ) (hH4 : Even b) :
    Odd (a - b) := by
  -- 1. mun:divisibility-odd-minus-even, from H2, H4
  exact (Parley.Items.Stdlib.Divisibility.mun_odd_minus_even (a := a) hH2 (b := b) hH4)

end Parley.Tests.Stdlib.Divisibility.OddMinusEven
