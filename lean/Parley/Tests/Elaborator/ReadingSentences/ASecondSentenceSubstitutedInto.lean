module

public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceSubstitutedInto

theorem a_second_sentence_substituted_into (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : a < b) (hH4 : b = 2) :
    a < 2 := by
  -- 1. substitute b = 2 (H4) into H3
  parley_subst_at hH4 hH3b

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceSubstitutedInto
