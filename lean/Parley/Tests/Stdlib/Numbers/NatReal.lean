module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NatReal

theorem nat_real (m : ℤ) (hH1 : 0 < m) :
    True := by
  -- 1. mun:numbers-nat-real
  exact trivial

end Parley.Tests.Stdlib.Numbers.NatReal
