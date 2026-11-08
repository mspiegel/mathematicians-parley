module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/unfolding-the-named-sentence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.UnfoldingTheNamedSentence.TheSecondSentenceUnfolded

theorem the_second_sentence_unfolded {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ B ∧ A ⊆ C) :
    (∀ t ∈ A, t ∈ C) := by
  -- 1. def:subset X := A, Y := C, from H4
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp hH4.2

end Parley.Tests.Elaborator.UnfoldingTheNamedSentence.TheSecondSentenceUnfolded
