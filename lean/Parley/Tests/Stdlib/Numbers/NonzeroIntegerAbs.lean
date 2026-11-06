module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NonzeroIntegerAbs

theorem nonzero_integer_abs (m : ℤ) (hH2 : m ≠ 0) :
    abs m ≥ 1 := by
  -- 1. mun:numbers-nonzero-integer-abs z := m, from H2
  have s1 : abs m ≥ 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_nonzero_integer_abs (z := m) hH2)] | (have h := (Parley.Items.Stdlib.Numbers.mun_nonzero_integer_abs (z := m) hH2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonzero_integer_abs (z := m) hH2) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonzero_integer_abs (z := m) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.NonzeroIntegerAbs
