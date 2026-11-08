module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AnOrderAndItsConverse

theorem an_order_and_its_converse (a : ℝ) (b : ℝ) (hH3 : a ≤ b) (hH4 : a ≥ b) :
    b = a := by
  -- 1. antisymmetry, from H3, H4
  parley_side

end Parley.Tests.Elaborator.Transitivity.AnOrderAndItsConverse
