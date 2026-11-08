module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.IntReal

theorem int_real (m : ℤ) :
    True := by
  -- 1. mun:numbers-int-real
  exact trivial

end Parley.Tests.Stdlib.Numbers.IntReal
