module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/a-letter-for-a-conjunction.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALetterForAConjunction.AConjunctionConcludedAsALetter

theorem a_conjunction_concluded_as_a_letter (x : ℝ) (hH2 : x = 0 ↔ 0 ≤ x ∧ x < 1) (hH3 : x = 0) :
    (0 ≤ x ∧ x < 1) := by
  -- 1. mun:iff-from-left P := x = 0, Q := 0 ≤ x and x < 1, from H2, H3
  have s1 : 0 ≤ x ∧ x < 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := 0 ≤ x ∧ x < 1) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := 0 ≤ x ∧ x < 1) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := 0 ≤ x ∧ x < 1) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := 0 ≤ x ∧ x < 1) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := 0 ≤ x ∧ x < 1) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ALetterForAConjunction.AConjunctionConcludedAsALetter
