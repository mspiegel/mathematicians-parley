module

public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAsTheSubstitutedEquation

theorem a_second_sentence_as_the_substituted_equation (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    a + b = a + 2 := by
  -- 1. substitute b = 2 (H3)
  parley_subst hH3b

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAsTheSubstitutedEquation
