module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInACalculationLink

theorem a_second_sentence_in_a_calculation_link (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    b = 1 + 1 := by
  -- 1. calculation
  calc b = 2 := by parley_side
    _ = 1 + 1 := by norm_num

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInACalculationLink
