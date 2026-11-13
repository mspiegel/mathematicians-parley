module

public import NormTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.OneMultipliedOneAdded

theorem one_multiplied_one_added (x : ℝ) (y : ℝ) (z : ℝ) (hH4 : y = 1) (hH5 : z = 2) :
    x * y + z = x + 2 := by
  -- 1. algebra, from H4, H5
  linear_combination (norm := parley_norm) (x) * hH4 + hH5

end Parley.Tests.Elaborator.Combinations.OneMultipliedOneAdded
