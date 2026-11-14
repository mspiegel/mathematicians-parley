module

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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/order-chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OrderChains.AnEquationBetweenTwoBounds

theorem an_equation_between_two_bounds (x : ℝ) (y : ℝ) (hH3 : 0 ≤ y) :
    x < 1 + x + y := by
  -- 1. inequalities
  have s1 : x < x + 1 := by linarith
  -- 2. algebra
  have s2 : x + 1 = 1 + x := by ring1
  -- 3. inequalities
  have s3 : 1 + x ≤ 1 + x + y := by linarith only [hH3]
  -- 4. calculation
  calc x < x + 1 := s1
    _ = 1 + x := s2
    _ ≤ 1 + x + y := s3

end Parley.Tests.Elaborator.OrderChains.AnEquationBetweenTwoBounds
