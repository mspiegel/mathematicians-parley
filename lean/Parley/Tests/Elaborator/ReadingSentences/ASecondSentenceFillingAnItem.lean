module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceFillingAnItem

theorem a_second_sentence_filling_an_item (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    (b = 0 ∨ b = 2) := by
  -- 1. mun:or-right P := b = 0, Q := b = 2, from H3
  have s1 : b = 0 ∨ b = 2 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3b) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3b)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3b) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3b) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3b); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceFillingAnItem
