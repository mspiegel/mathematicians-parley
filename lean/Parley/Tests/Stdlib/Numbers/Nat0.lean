module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0

theorem nat0 (n : ℝ) (hH2 : ∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = n) :
    ((∃ m : ℤ, 0 < m ∧ (m : ℝ) = n) ∨ n = 0) := by
  -- 1. def:numbers-nat0, from H2
  exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := n))).mp hH2

end Parley.Tests.Stdlib.Numbers.Nat0
