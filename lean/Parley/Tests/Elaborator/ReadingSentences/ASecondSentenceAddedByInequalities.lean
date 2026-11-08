module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAddedByInequalities

theorem a_second_sentence_added_by_inequalities (a : ℝ) (b : ℝ) (c : ℝ) (hH4a : a = 1) (hH4b : b > 0) (hH5 : c > 0) :
    b + c > 0 := by
  -- 1. inequalities, from H4, H5
  parley_order

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAddedByInequalities
