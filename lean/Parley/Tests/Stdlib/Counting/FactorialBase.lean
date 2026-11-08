module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialBase

theorem factorial_base :
    (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by
  -- 1. def:factorial
  exact Parley.Items.Stdlib.Counting.def_factorial_2

end Parley.Tests.Stdlib.Counting.FactorialBase
