module

public import LeanBridges
public import Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedBesideALetterOfTheSameName

theorem cited_beside_a_letter_of_the_same_name (C : ℝ) (D : ℝ) :
    D + D - D = D := by
  -- 1. thm:a-double-less-one
  have s1 : D + D - D = D := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D)) | (have h := (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D)) | exact_mod_cast ((Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D))).symm | (have h := (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne.a_double_less_one (C := D)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedBesideALetterOfTheSameName
