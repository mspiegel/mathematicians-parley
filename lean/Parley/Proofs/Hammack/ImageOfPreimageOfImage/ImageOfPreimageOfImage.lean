module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage

/-! Written from proofs/hammack/image-of-preimage-of-image.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfPreimageOfImage.ImageOfPreimageOfImage

set_option maxHeartbeats 400000 in
theorem image_of_preimage_of_image {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (X : Set α) (hH4 : X ⊆ A) :
    f '' (A ∩ (A ∩ f ⁻¹' (f '' (A ∩ X)))) = f '' (A ∩ X) := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ f ⁻¹' (f '' (A ∩ X)), u ∈ A := by
    intro u hK1
    -- 1.1. def:preimage Z := f[X], from K1
    exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK1).1
  -- 2. def:subset, from 1
  have s2 : A ∩ f ⁻¹' (f '' (A ∩ X)) ⊆ A := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (f '' (A ∩ X))) (Y := A))).mpr s1
  -- 3. proof
  have s3 : ∀ y ∈ f '' (A ∩ (A ∩ f ⁻¹' (f '' (A ∩ X)))), y ∈ f '' (A ∩ X) := by
    intro y hK2
    -- 3.1. obtain s: def:image u := y, Y := f⁻¹[f[X]], from K2, 2
    obtain ⟨s, s3_1a, s3_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := A ∩ f ⁻¹' (f '' (A ∩ X))) (f := f) (u := y) (W := Set.univ) s2 (by parley_set_side))).mp hK2
    -- 3.2. def:preimage u := s, Z := f[X], from 3.1
    have s3_2a : s ∈ A := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp s3_1a).1
    have s3_2b : f s ∈ f '' (A ∩ X) := by simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := f '' (A ∩ X)) (f := f) (u := s) (W := Set.univ) (by parley_set_side))).mp s3_1a).2
    -- 3.3. substitute y = f(s) (line 3.1) into line 3.2
    parley_subst_at s3_1b s3_2b
  -- 4. def:subset, from 3
  have s4 : f '' (A ∩ (A ∩ f ⁻¹' (f '' (A ∩ X)))) ⊆ f '' (A ∩ X) := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (A ∩ (A ∩ f ⁻¹' (f '' (A ∩ X))))) (Y := f '' (A ∩ X)))).mpr s3
  -- 5. thm:subset-of-preimage-of-image, from H4
  have s5 : X ⊆ A ∩ f ⁻¹' (f '' (A ∩ X)) := by exact (Parley.Proofs.Hammack.PreimageOfImage.SubsetOfPreimageOfImage.subset_of_preimage_of_image (A := A) (B := Set.univ) (f := f) (by parley_set_side) (X := X) (by parley_set_side))
  -- 6. mun:image-monotone Y := X, Z := f⁻¹[f[X]], from 5
  have s6 : f '' (A ∩ X) ⊆ f '' (A ∩ (A ∩ f ⁻¹' (f '' (A ∩ X)))) := by exact (Parley.Items.Stdlib.Functions.mun_image_monotone (X := A) (Y := X) (Z := A ∩ f ⁻¹' (f '' (A ∩ X))) (f := f) (W := Set.univ) s5 (by parley_set_side))
  -- 7. mun:subset-antisymmetric, from 4, 6
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (A ∩ (A ∩ f ⁻¹' (f '' (A ∩ X))))) (Y := f '' (A ∩ X)) s4 s6)

end Parley.Proofs.Hammack.ImageOfPreimageOfImage.ImageOfPreimageOfImage
