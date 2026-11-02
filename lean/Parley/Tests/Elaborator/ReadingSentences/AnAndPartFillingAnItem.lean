module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartFillingAnItem

theorem an_and_part_filling_an_item (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    (b = 0 ∨ b = 2) := by
  -- 1. mun:or-right P := b = 0, Q := b = 2, from H3
  have s1 : b = 0 ∨ b = 2 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := b = 2) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartFillingAnItem
