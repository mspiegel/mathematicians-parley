module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/preimage-of-image-of-preimage.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfImageOfPreimage.PreimageOfImageOfPreimage

theorem preimage_of_image_of_preimage {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (f : α → β) (hH3 : Set.MapsTo f A B) (Y : Set β) (hH4 : Y ⊆ B) :
    A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y))) = A ∩ f ⁻¹' Y := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ f ⁻¹' Y, u ∈ A := by
    intro u hK1
    -- 1.1. def:preimage Z := Y, from K1
    exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := B) hH3)).mp hK1).1
  -- 2. def:subset, from 1
  have s2 : A ∩ f ⁻¹' Y ⊆ A := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y) (Y := A))).mpr s1
  -- 3. proof
  have s3 : ∀ u ∈ A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y))), u ∈ A ∩ f ⁻¹' Y := by
    intro u hK2
    -- 3.1. def:preimage Z := f[f⁻¹[Y]], from K2
    have s3_1a : u ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ (A ∩ f ⁻¹' Y))) (f := f) (u := u) (W := B) hH3)).mp hK2).1
    have s3_1b : f u ∈ f '' (A ∩ (A ∩ f ⁻¹' Y)) := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ (A ∩ f ⁻¹' Y))) (f := f) (u := u) (W := B) hH3)).mp hK2).2
    -- 3.2. obtain s: def:image u := f(u), Y := f⁻¹[Y], from 2, 3.1
    obtain ⟨s, s3_2a, s3_2b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (u := f u) (W := Set.univ) s2 (Set.mapsTo_univ _ _))).mp s3_1b
    -- 3.3. def:preimage u := s, Z := Y, from 3.2
    have s3_3a : s ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := B) hH3)).mp s3_2a).1
    have s3_3b : f s ∈ Y := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := s) (W := B) hH3)).mp s3_2a).2
    -- 3.4. substitute f(u) = f(s) (line 3.2) into line 3.3
    have s3_4 : f u ∈ Y := Eq.subst (motive := (fun t : β => t ∈ Y)) s3_2b.symm s3_3b
    -- 3.5. def:preimage Z := Y, from 3.1, 3.4
    exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := B) hH3)).mpr ⟨s3_1a, s3_4⟩
  -- 4. def:subset, from 3
  have s4 : A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y))) ⊆ A ∩ f ⁻¹' Y := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y)))) (Y := A ∩ f ⁻¹' Y))).mpr s3
  -- 5. proof
  have s5 : ∀ u ∈ A ∩ f ⁻¹' Y, u ∈ A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y))) := by
    intro u hK3
    -- 5.1. def:preimage Z := Y, from K3
    have s5_1a : u ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := B) hH3)).mp hK3).1
    have s5_1b : f u ∈ Y := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := B) hH3)).mp hK3).2
    -- 5.2. mun:value-in-image Y := f⁻¹[Y], from K3, 2
    have s5_2 : f u ∈ f '' (A ∩ (A ∩ f ⁻¹' Y)) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A ∩ f ⁻¹' Y) (f := f) (s := u) (W := B) s2 hK3 hH3)
    -- 5.3. def:preimage Z := f[f⁻¹[Y]], from 5.1, 5.2
    exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ (A ∩ f ⁻¹' Y))) (f := f) (u := u) (W := B) hH3)).mpr ⟨s5_1a, s5_2⟩
  -- 6. def:subset, from 5
  have s6 : A ∩ f ⁻¹' Y ⊆ A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y))) := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y) (Y := A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y)))))).mpr s5
  -- 7. mun:subset-antisymmetric, from 4, 6
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (f '' (A ∩ (A ∩ f ⁻¹' Y)))) (Y := A ∩ f ⁻¹' Y) s4 s6)

end Parley.Proofs.Hammack.PreimageOfImageOfPreimage.PreimageOfImageOfPreimage
