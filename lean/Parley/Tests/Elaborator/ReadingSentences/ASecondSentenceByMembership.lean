module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership

theorem a_second_sentence_by_membership (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : ∃ m : ℝ, (m : ℂ) = (b : ℂ) ^ (1 / 2 : ℂ)) :
    (∃ m : ℝ, (m : ℂ) = (b : ℂ) ^ (1 / 2 : ℂ) + 1) := by
  -- 1. membership, from H3
  have s1 : ∃ m : ℝ, (m : ℂ) = (b : ℂ) ^ (1 / 2 : ℂ) + 1 := by (exact ⟨(Classical.choose hH3b : ℝ) + 1, by push_cast; (try simp only [Classical.choose_spec hH3b]); first | done | parley_ring⟩)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership
