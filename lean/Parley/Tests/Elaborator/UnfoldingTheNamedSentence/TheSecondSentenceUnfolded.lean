module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/unfolding-the-named-sentence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.UnfoldingTheNamedSentence.TheSecondSentenceUnfolded

theorem the_second_sentence_unfolded {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ B ∧ A ⊆ C) :
    (∀ t ∈ A, t ∈ C) := by
  -- 1. def:subset X := A, Y := C, from H4
  have s1 : ∀ t ∈ A, t ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp (by parley_side); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.UnfoldingTheNamedSentence.TheSecondSentenceUnfolded
