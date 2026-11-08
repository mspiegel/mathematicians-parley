module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight

theorem in_a_union_on_the_right {α : Type*} (A : Set α) (B : Set α) :
    A ⊆ B ∪ A := by
  -- 1. proof
  have s1 : ∀ u ∈ A, u ∈ B ∪ A := by
    intro u hK1
    -- 1.1. mun:in-union-right, from K1
    exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) hK1)
  -- 2. def:subset, from 1
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A))).mpr s1; parley_set_side)

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.InAUnionOnTheRight
