module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/order-chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OrderChains.AnEquationBetweenTwoBounds

theorem an_equation_between_two_bounds (x : ℝ) (y : ℝ) (hH3 : 0 ≤ y) :
    x < 1 + x + y := by
  -- 1. inequalities
  have s1 : x < x + 1 := by parley_order
  -- 2. algebra
  have s2 : x + 1 = 1 + x := by parley_ring
  -- 3. inequalities
  have s3 : 1 + x ≤ 1 + x + y := by parley_order
  -- 4. calculation
  have s4 : x < 1 + x + y := by
    calc x < x + 1 := by parley_side
      _ = 1 + x := by parley_side
      _ ≤ 1 + x + y := by parley_side
  all_goals exact s4

end Parley.Tests.Elaborator.OrderChains.AnEquationBetweenTwoBounds
