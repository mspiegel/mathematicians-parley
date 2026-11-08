module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInstantiated

theorem a_second_sentence_instantiated (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : ∀ x : ℝ, x * 0 = 0) :
    b * 0 = 0 := by
  -- 1. instantiate x := b in H3
  exact (hH3b b)

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInstantiated
