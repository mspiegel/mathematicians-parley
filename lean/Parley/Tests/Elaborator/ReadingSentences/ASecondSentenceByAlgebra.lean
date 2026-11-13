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

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByAlgebra

theorem a_second_sentence_by_algebra (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    b * b = 4 := by
  -- 1. algebra, from H3
  linear_combination (norm := parley_norm) (b + 2) * hH3b

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByAlgebra
