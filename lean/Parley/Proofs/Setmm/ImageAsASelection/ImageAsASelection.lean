module

public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/image-as-a-selection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageAsASelection.ImageAsASelection

set_option maxHeartbeats 400000 in
theorem image_as_a_selection {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B) (X : Set α) (hH4 : X ⊆ A) :
    F '' (A ∩ X) = {y ∈ B | ∃ x ∈ X, F x = y} := by
  -- 1. proof
  have s1 : ∀ u ∈ F '' (A ∩ X), u ∈ {y ∈ B | ∃ x ∈ X, F x = y} := by
    intro u hK1
    -- 1.1. def:image X := A, Y := X, from H4, K1
    have s1_1 : ∃ s ∈ X, u = F s := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := X) (f := F) (u := u) (W := Set.univ) hH4 (by parley_set_side))).mp (by parley_set_side)
    -- 1.2. obtain s from line 1.1
    obtain ⟨s, s1_2a, s1_2b⟩ := s1_1
    -- 1.3. mun:in-subset, from H4, 1.2
    have s1_3 : s ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) hH4 s1_2a)
    -- 1.4. mun:function-value f := F, x := s, from 1.3
    have s1_4 : F s ∈ B := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := F) (x := s) s1_3 (by parley_set_side))
    -- 1.5. substitute u = F(s) (line 1.2) into line 1.4
    have s1_5 : u ∈ B := by parley_subst_at s1_2b s1_4
    -- 1.6. exhibit, from 1.2
    have s1_6 : ∃ x ∈ X, F x = u := ⟨s, by parley_set_side, by parley_set_side⟩
    -- 1.7. def:set-builder, from 1.5, 1.6
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : α => ∃ x ∈ X, F x = y)) (X := B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : α => ∃ x ∈ X, F x = y)) (X := B) (u := u))).mpr (by parley_set_side); parley_set_side)
  -- 2. def:subset, from 1
  have s2 : F '' (A ∩ X) ⊆ {y ∈ B | ∃ x ∈ X, F x = y} := ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ X)) (Y := {y ∈ B | ∃ x ∈ X, F x = y}))).mpr s1
  -- 3. proof
  have s3 : ∀ u ∈ {y ∈ B | ∃ x ∈ X, F x = y}, u ∈ F '' (A ∩ X) := by
    intro u hK2
    -- 3.1. def:set-builder, from K2
    have s3_1 : ∃ x ∈ X, F x = u := by first | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : α => ∃ x ∈ X, F x = y)) (X := B) (u := u))).mp hK2 | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : α => ∃ x ∈ X, F x = y)) (X := B) (u := u))).mp hK2).symm | simpa using ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : α => ∃ x ∈ X, F x = y)) (X := B) (u := u))).mp hK2 | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : α => ∃ x ∈ X, F x = y)) (X := B) (u := u))).mp hK2 | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun y : α => ∃ x ∈ X, F x = y)) (X := B) (u := u))).mp hK2; parley_set_side)
    -- 3.2. obtain x from line 3.1
    obtain ⟨x, s3_2a, s3_2b⟩ := s3_1
    -- 3.3. mun:value-in-image, from H4, 3.2
    have s3_3 : F x ∈ F '' (A ∩ X) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3_2a (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3_2a (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3_2a (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3_2a (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := Set.univ) hH4 s3_2a (by parley_set_side)); parley_set_side)
    -- 3.4. substitute F(x) = u (line 3.2) into line 3.3
    parley_subst_at s3_2b s3_3
  -- 4. def:subset, from 3
  have s4 : {y ∈ B | ∃ x ∈ X, F x = y} ⊆ F '' (A ∩ X) := ((Parley.Items.Stdlib.Sets.def_subset (X := {y ∈ B | ∃ x ∈ X, F x = y}) (Y := F '' (A ∩ X)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ X)) (Y := {y ∈ B | ∃ x ∈ X, F x = y}) s2 s4)

end Parley.Proofs.Setmm.ImageAsASelection.ImageAsASelection
