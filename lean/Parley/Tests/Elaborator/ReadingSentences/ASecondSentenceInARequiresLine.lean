module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInARequiresLine

theorem a_second_sentence_in_a_requires_line (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b > 0) :
    a / b * b = a := by
  -- 1. algebra
  have r64_1 : b ≠ 0 := by parley_side
  have s1 : a / b * b = a := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInARequiresLine
