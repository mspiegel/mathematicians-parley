module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedWithItsLettersSwapped

theorem cited_with_its_letters_swapped {α : Type*} (A : Set α) (B : Set α) :
    B ⊆ A ∪ B := by
  -- 1. thm:in-a-union-on-the-right
  exact (Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight.in_a_union_on_the_right (A := B) (B := A))

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.CitedWithItsLettersSwapped
