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
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/unfolding-the-named-sentence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.UnfoldingTheNamedSentence.TheSecondSentenceUnfolded

theorem the_second_sentence_unfolded {α : Type*} [Nonempty α] (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ B ∧ A ⊆ C) :
    (∀ t ∈ A, t ∈ C) := by
  -- 1. def:subset X := A, Y := C, from H4
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp hH4.2

end Parley.Tests.Elaborator.UnfoldingTheNamedSentence.TheSecondSentenceUnfolded
