module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialStep

theorem factorial_step (n : ℤ) (hH1 : 0 ≤ n) :
    (LeanBridges.Counting.factorial (n + 1) : ℤ) = (LeanBridges.Counting.factorial n : ℤ) * (n + 1) := by
  -- 1. def:factorial
  exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) hH1)

end Parley.Tests.Stdlib.Counting.FactorialStep
