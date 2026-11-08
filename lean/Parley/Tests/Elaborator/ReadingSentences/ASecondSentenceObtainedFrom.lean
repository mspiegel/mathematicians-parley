module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceObtainedFrom

theorem a_second_sentence_obtained_from (a : ℝ) (b : ℤ) (hH3a : a = 1) (hH3b : ∃ k : ℤ, b = 2 * k) :
    (∃ j : ℤ, b = 2 * j) := by
  -- 1. obtain k from H3
  obtain ⟨k, s1⟩ := hH3b
  -- 2. exhibit, from 1
  exact ⟨k, s1⟩

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceObtainedFrom
