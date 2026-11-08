module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.AFractionNotNatural

theorem a_fraction_not_natural :
    ¬ (∃ m : ℤ, 0 < m ∧ (m : ℚ) = 1 / 76) := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.ClosedValues.AFractionNotNatural
