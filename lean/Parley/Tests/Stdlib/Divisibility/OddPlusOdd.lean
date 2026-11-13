module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.OddPlusOdd

theorem odd_plus_odd (a : ℤ) (hH2 : Odd a) (b : ℤ) (hH4 : Odd b) :
    Even (a + b) := by
  -- 1. mun:divisibility-odd-plus-odd, from H2, H4
  exact (Parley.Items.Stdlib.Divisibility.mun_odd_plus_odd (a := a) hH2 (b := b) hH4)

end Parley.Tests.Stdlib.Divisibility.OddPlusOdd
