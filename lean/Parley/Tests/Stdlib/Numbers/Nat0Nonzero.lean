module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0Nonzero

theorem nat0_nonzero (m : ℤ) (hH1 : 0 ≤ m) (hH2 : m ≠ 0) :
    0 < m := by
  -- 1. mun:numbers-nat0-nonzero, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) hH1 hH2)

end Parley.Tests.Stdlib.Numbers.Nat0Nonzero
