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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Chains.APairOnACalculationLine

theorem a_pair_on_a_calculation_line (w : ℝ) (x : ℝ) (y : ℝ) (z : ℝ) (hH5 : x = y ∧ y = z) (hH6 : w = x) :
    w = z := by
  -- 1. calculation
  calc w = x := hH6
    _ = z := Eq.trans (hH5.1) hH5.2

end Parley.Tests.Elaborator.Chains.APairOnACalculationLine
