module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NonzeroIntegerAbs

theorem nonzero_integer_abs (m : ℤ) (hH2 : m ≠ 0) :
    abs m ≥ 1 := by
  -- 1. mun:numbers-nonzero-integer-abs z := m, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_nonzero_integer_abs (z := m) hH2)

end Parley.Tests.Stdlib.Numbers.NonzeroIntegerAbs
