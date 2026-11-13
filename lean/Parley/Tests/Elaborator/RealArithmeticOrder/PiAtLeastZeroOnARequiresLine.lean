module

public import Divisibility
public import RealTactics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
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
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiAtLeastZeroOnARequiresLine

theorem pi_at_least_zero_on_a_requires_line (N : ℝ) (hH2 : Real.pi < N) :
    LeanBridges.Divisibility.mod Real.pi N = Real.pi := by
  -- 1. mun:mod-below a := π, b := N, from H2
  have r115_1 : 0 ≤ Real.pi := by parley_real
  exact (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) r115_1 hH2)

end Parley.Tests.Elaborator.RealArithmeticOrder.PiAtLeastZeroOnARequiresLine
