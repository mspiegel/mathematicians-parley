module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0Int

theorem nat0_int (m : ℤ) (hH1 : 0 ≤ m) :
    True := by
  -- 1. mun:numbers-nat0-int
  exact trivial

end Parley.Tests.Stdlib.Numbers.Nat0Int
