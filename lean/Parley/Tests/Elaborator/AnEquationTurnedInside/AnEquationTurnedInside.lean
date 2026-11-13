module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/an-equation-turned-inside.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnEquationTurnedInside.AnEquationTurnedInside

theorem an_equation_turned_inside (x : ℝ) (y : ℝ) (hH3 : x = 1 ↔ y + 0 = 2) (hH4 : 2 ≠ y) :
    x ≠ 1 := by
  -- 1. mun:iff-not-from-right, from H3, H4
  exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 1) (Q := y + 0 = 2) hH3 (by simpa only [add_zero] using Ne.symm hH4))

end Parley.Tests.Elaborator.AnEquationTurnedInside.AnEquationTurnedInside
