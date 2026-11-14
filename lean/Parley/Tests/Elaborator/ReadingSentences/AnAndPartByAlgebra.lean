module

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

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartByAlgebra

theorem an_and_part_by_algebra (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    b * b = 4 := by
  -- 1. algebra, from H3
  linear_combination (b + 2) * hH3.2

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartByAlgebra
