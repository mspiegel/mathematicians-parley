module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership

theorem a_second_sentence_by_membership (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : ∃ m : ℝ, (m : ℂ) = (b : ℂ) ^ (1 / 2 : ℂ)) :
    (∃ m : ℝ, (m : ℂ) = (b : ℂ) ^ (1 / 2 : ℂ) + 1) := by
  -- 1. membership, from H3
  (exact ⟨(Classical.choose hH3b : ℝ) + 1, by push_cast; (try simp only [Classical.choose_spec hH3b]); all_goals parley_ring⟩)

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership
