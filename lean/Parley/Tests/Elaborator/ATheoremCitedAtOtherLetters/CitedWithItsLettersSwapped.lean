module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedWithItsLettersSwapped

theorem cited_with_its_letters_swapped {α : Type*} (A : Set α) (B : Set α) :
    B ⊆ A ∪ B := by
  -- 1. thm:in-a-union-on-the-right
  have s1 : B ⊆ A ∪ B := by first | exact (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight.in_a_union_on_the_right (A := B) (B := A)) | exact ((Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight.in_a_union_on_the_right (A := B) (B := A))).symm | simpa using (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight.in_a_union_on_the_right (A := B) (B := A)) | exact_mod_cast (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight.in_a_union_on_the_right (A := B) (B := A)) | (have h := (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight.in_a_union_on_the_right (A := B) (B := A)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedWithItsLettersSwapped
