module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/preimage-of-image.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage

theorem subset_of_preimage_of_image {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (f : α → β) (hH3 : Set.MapsTo f A B) (X : Set α) (hH4 : X ⊆ A) :
    X ⊆ A ∩ f ⁻¹' (f '' (A ∩ X)) := by
  -- 1. proof
  have s1 : ∀ x ∈ X, x ∈ A ∩ f ⁻¹' (f '' (A ∩ X)) := by
    intro x hK1
    -- 1.1. mun:in-subset, from H4, K1
    have s1_1 : x ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := x) hH4 hK1)
    -- 1.2. mun:value-in-image, from H4, K1
    have s1_2 : f x ∈ f '' (A ∩ X) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := x) (W := B) hH4 hK1 hH3)
    -- 1.3. def:preimage u := x, from 1.1, 1.2
    exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := x) (W := B) hH3)).mpr ⟨s1_1, s1_2⟩
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := A ∩ f ⁻¹' (f '' (A ∩ X))))).mpr s1

end Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage
