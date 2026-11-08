module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAsAFirstRow

theorem a_second_sentence_as_a_first_row (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b > 0) :
    b + 1 > 1 := by
  -- 1. inequalities
  parley_order

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAsAFirstRow
