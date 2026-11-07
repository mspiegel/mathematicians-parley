module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartFillingAnItem

theorem an_and_part_filling_an_item (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    (b = 0 ∨ b = 2) := by
  -- 1. mun:or-right P := b = 0, Q := b = 2, from H3
  have s1 : b = 0 ∨ b = 2 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3.2) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3.2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3.2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3.2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) hH3.2); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartFillingAnItem
