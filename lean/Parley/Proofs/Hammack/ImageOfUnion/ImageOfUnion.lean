module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfUnion.ImageOfUnion

theorem image_of_union {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (W : Set α) (hH4 : W ⊆ A) (X : Set α) (hH5 : X ⊆ A) :
    f '' (W ∪ X) = f '' W ∪ f '' X := by
  -- 1. mun:union-subset, from H4, H5
  have s1 : W ∪ X ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := X) (Z := A) hH4 hH5) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := X) (Z := A) hH4 hH5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := X) (Z := A) hH4 hH5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := X) (Z := A) hH4 hH5) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := X) (Z := A) hH4 hH5); parley_set_side)
  -- 2. proof
  have s2 : ∀ y ∈ f '' (W ∪ X), y ∈ f '' W ∪ f '' X := by
    intro y hK1
    -- 2.1. obtain s: def:image u := y, Y := W ∪ X, from K1, 1
    obtain ⟨s, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := W ∪ X) (f := f) (u := y) (W := Set.univ) (by parley_set_side) s1)).mp (by parley_set_side)
    -- 2.2. def:union u := s, Y := W, Z := X, from 2.1
    have s2_2 : s ∈ W ∨ s ∈ X := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side); parley_set_side)
    -- 2.3. cases, from 2.2
    have s2_3 : y ∈ f '' W ∪ f '' X := by
      rcases s2_2 with hC1 | hC2
      · skip
        -- 2.3.1. mun:value-in-image Y := W, from C1, H4
        have s2_3_1 : f s ∈ f '' W := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH4 hC1) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH4 hC1)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH4 hC1) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH4 hC1) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH4 hC1); parley_set_side)
        -- 2.3.2. substitute y = f(s) (line 2.1) into line 2.3.1
        have s2_3_2 : y ∈ f '' W := by parley_subst_at s2_1b s2_3_1
        -- 2.3.3. mun:in-union-left Y := f[W], Z := f[X], from 2.3.2
        have s2_3_3 : y ∈ f '' W ∪ f '' X := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := f '' W) (Z := f '' X) (u := y) s2_3_2) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := f '' W) (Z := f '' X) (u := y) s2_3_2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := f '' W) (Z := f '' X) (u := y) s2_3_2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := f '' W) (Z := f '' X) (u := y) s2_3_2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := f '' W) (Z := f '' X) (u := y) s2_3_2); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 2.3.4. mun:value-in-image Y := X, from C2, H5
        have s2_3_4 : f s ∈ f '' X := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH5 hC2) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH5 hC2)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH5 hC2) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH5 hC2) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := Set.univ) (by parley_set_side) hH5 hC2); parley_set_side)
        -- 2.3.5. substitute y = f(s) (line 2.1) into line 2.3.4
        have s2_3_5 : y ∈ f '' X := by parley_subst_at s2_1b s2_3_4
        -- 2.3.6. mun:in-union-right Y := f[W], Z := f[X], from 2.3.5
        have s2_3_6 : y ∈ f '' W ∪ f '' X := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := f '' W) (Z := f '' X) (u := y) s2_3_5) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := f '' W) (Z := f '' X) (u := y) s2_3_5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := f '' W) (Z := f '' X) (u := y) s2_3_5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := f '' W) (Z := f '' X) (u := y) s2_3_5) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := f '' W) (Z := f '' X) (u := y) s2_3_5); parley_set_side)
        all_goals parley_set_side
    all_goals exact s2_3
  -- 3. def:subset, from 2
  have s3 : f '' (W ∪ X) ⊆ f '' W ∪ f '' X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (W ∪ X)) (Y := f '' W ∪ f '' X))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (W ∪ X)) (Y := f '' W ∪ f '' X))).mpr (by parley_set_side); parley_set_side)
  -- 4. proof
  have s4 : ∀ t ∈ W, t ∈ W ∪ X := by
    intro t hK2
    -- 4.1. mun:in-union-left Y := W, Z := X, from K2
    have s4_1 : t ∈ W ∪ X := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := W) (Z := X) (u := t) hK2) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := W) (Z := X) (u := t) hK2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := W) (Z := X) (u := t) hK2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := W) (Z := X) (u := t) hK2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := W) (Z := X) (u := t) hK2); parley_set_side)
    all_goals exact s4_1
  -- 5. def:subset, from 4
  have s5 : W ⊆ W ∪ X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := W) (Y := W ∪ X))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := W) (Y := W ∪ X))).mpr (by parley_set_side); parley_set_side)
  -- 6. mun:image-monotone Y := W, Z := W ∪ X, from 5
  have s6 : f '' W ⊆ f '' (W ∪ X) := by first | exact (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := W) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s5) | exact ((Parley.Items.Stdlib.Functions.mun_image_monotone (Y := W) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s5)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := W) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s5) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := W) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s5) | (have h := (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := W) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s5); parley_set_side)
  -- 7. proof
  have s7 : ∀ t ∈ X, t ∈ W ∪ X := by
    intro t hK3
    -- 7.1. mun:in-union-right Y := W, Z := X, from K3
    have s7_1 : t ∈ W ∪ X := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := W) (Z := X) (u := t) hK3) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := W) (Z := X) (u := t) hK3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := W) (Z := X) (u := t) hK3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := W) (Z := X) (u := t) hK3) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := W) (Z := X) (u := t) hK3); parley_set_side)
    all_goals exact s7_1
  -- 8. def:subset, from 7
  have s8 : X ⊆ W ∪ X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := W ∪ X))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := W ∪ X))).mpr (by parley_set_side); parley_set_side)
  -- 9. mun:image-monotone Y := X, Z := W ∪ X, from 8
  have s9 : f '' X ⊆ f '' (W ∪ X) := by first | exact (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := X) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s8) | exact ((Parley.Items.Stdlib.Functions.mun_image_monotone (Y := X) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s8)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := X) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s8) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := X) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s8) | (have h := (Parley.Items.Stdlib.Functions.mun_image_monotone (Y := X) (Z := W ∪ X) (f := f) (X := Set.univ) (W := Set.univ) (by parley_set_side) s8); parley_set_side)
  -- 10. mun:union-subset X := f[W], Y := f[X], Z := f[W ∪ X], from 6, 9
  have s10 : f '' W ∪ f '' X ⊆ f '' (W ∪ X) := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := f '' W) (Y := f '' X) (Z := f '' (W ∪ X)) s6 s9) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := f '' W) (Y := f '' X) (Z := f '' (W ∪ X)) s6 s9)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := f '' W) (Y := f '' X) (Z := f '' (W ∪ X)) s6 s9) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := f '' W) (Y := f '' X) (Z := f '' (W ∪ X)) s6 s9) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := f '' W) (Y := f '' X) (Z := f '' (W ∪ X)) s6 s9); parley_set_side)
  -- 11. mun:subset-antisymmetric, from 3, 10
  have s11 : f '' (W ∪ X) = f '' W ∪ f '' X := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (W ∪ X)) (Y := f '' W ∪ f '' X) s3 s10) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (W ∪ X)) (Y := f '' W ∪ f '' X) s3 s10)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (W ∪ X)) (Y := f '' W ∪ f '' X) s3 s10) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (W ∪ X)) (Y := f '' W ∪ f '' X) s3 s10) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (W ∪ X)) (Y := f '' W ∪ f '' X) s3 s10); parley_set_side)
  all_goals exact s11

end Parley.Proofs.Hammack.ImageOfUnion.ImageOfUnion
