module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ZeroDivides

theorem zero_divides (n : ℤ) :
    ((0 : ℤ) ∣ n ↔ n = 0) := by
  -- 1. mun:divisibility-zero-divides
  exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n))

end Parley.Tests.Stdlib.Divisibility.ZeroDivides
