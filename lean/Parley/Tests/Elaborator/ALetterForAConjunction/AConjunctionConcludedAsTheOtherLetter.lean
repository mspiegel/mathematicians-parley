module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/a-letter-for-a-conjunction.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALetterForAConjunction.AConjunctionConcludedAsTheOtherLetter

theorem a_conjunction_concluded_as_the_other_letter (x : ℝ) (hH2 : 0 ≤ x ∧ x < 1 ↔ x = 0) (hH3 : x = 0) :
    (0 ≤ x ∧ x < 1) := by
  -- 1. mun:iff-from-right P := 0 ≤ x and x < 1, Q := x = 0, from H2, H3
  have s1 : 0 ≤ x ∧ x < 1 := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_right (P := 0 ≤ x ∧ x < 1) (Q := x = 0) hH2 hH3)
  all_goals exact s1

end Parley.Tests.Elaborator.ALetterForAConjunction.AConjunctionConcludedAsTheOtherLetter
