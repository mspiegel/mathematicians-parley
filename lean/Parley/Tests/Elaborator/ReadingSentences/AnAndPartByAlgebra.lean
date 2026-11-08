module

public import NormTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartByAlgebra

theorem an_and_part_by_algebra (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    b * b = 4 := by
  -- 1. algebra, from H3
  linear_combination (norm := parley_norm) (b + 2) * hH3.2

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartByAlgebra
