module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedBesideALetterOfTheSameName

theorem cited_beside_a_letter_of_the_same_name (C : ℝ) (D : ℝ) :
    D + D - D = D := by
  -- 1. thm:a-double-less-one
  have s1 : D + D - D = D := by exact (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D))
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedBesideALetterOfTheSameName
