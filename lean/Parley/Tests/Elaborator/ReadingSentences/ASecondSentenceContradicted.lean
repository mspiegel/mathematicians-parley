module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceContradicted

theorem a_second_sentence_contradicted (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b ≠ 2) :
    (b = 2 → a = 0) := by
  -- 1. proof
  intro hK1
  -- 1.1. restate K1
  have s1_1 : b = 2 := by exact hK1
  exact absurd s1_1 hH3b

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceContradicted
