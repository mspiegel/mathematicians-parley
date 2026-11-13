module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Defs.PartialOrder
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

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AnOrderAndItsConverse

theorem an_order_and_its_converse (a : ℝ) (b : ℝ) (hH3 : a ≤ b) (hH4 : a ≥ b) :
    b = a := by
  -- 1. antisymmetry, from H3, H4
  exact le_antisymm hH4 hH3

end Parley.Tests.Elaborator.Transitivity.AnOrderAndItsConverse
