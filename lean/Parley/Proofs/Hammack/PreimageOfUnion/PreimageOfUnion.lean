module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/preimage-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfUnion.PreimageOfUnion

set_option maxHeartbeats 400000 in
theorem preimage_of_union {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (Y : Set α) (hH4 : Y ⊆ B) (Z : Set α) (hH5 : Z ⊆ B) :
    A ∩ f ⁻¹' (Y ∪ Z) = A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ f ⁻¹' (Y ∪ Z), u ∈ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by
    intro u hK1
    -- 1.1. def:preimage Z := Y ∪ Z, from K1
    have s1_1a : u ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
    have s1_1b : f u ∈ Y ∪ Z := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. def:union u := f(u), from 1.1
    have s1_2 : f u ∈ Y ∨ f u ∈ Z := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := Y) (Z := Z) (u := f u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := Y) (Z := Z) (u := f u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := Y) (Z := Z) (u := f u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := Y) (Z := Z) (u := f u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := Y) (Z := Z) (u := f u))).mp (by parley_set_side); parley_set_side)
    -- 1.3. cases, from 1.2
    have s1_3 : u ∈ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by
      rcases s1_2 with hC1 | hC2
      · skip
        -- 1.3.1. def:preimage Z := Y, from C1, 1.1
        have s1_3_1 : u ∈ A ∩ f ⁻¹' Y := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
        -- 1.3.2. mun:in-union-left Y := f⁻¹[Y], Z := f⁻¹[Z], from 1.3.1
        have s1_3_2 : u ∈ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_1) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_1) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_1); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 1.3.3. def:preimage, from C2, 1.1
        have s1_3_3 : u ∈ A ∩ f ⁻¹' Z := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
        -- 1.3.4. mun:in-union-right Y := f⁻¹[Y], Z := f⁻¹[Z], from 1.3.3
        have s1_3_4 : u ∈ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_3) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_3) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_3); parley_set_side)
        all_goals parley_set_side
    all_goals exact s1_3
  -- 2. def:subset, from 1
  have s2 : A ∩ f ⁻¹' (Y ∪ Z) ⊆ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ u ∈ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z, u ∈ A ∩ f ⁻¹' (Y ∪ Z) := by
    intro u hK2
    -- 3.1. def:union Y := f⁻¹[Y], Z := f⁻¹[Z], from K2
    have s3_1 : u ∈ A ∩ f ⁻¹' Y ∨ u ∈ A ∩ f ⁻¹' Z := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 3.2. cases, from 3.1
    have s3_2 : u ∈ A ∩ f ⁻¹' (Y ∪ Z) := by
      rcases s3_1 with hC3 | hC4
      · skip
        -- 3.2.1. def:preimage Z := Y, from C3
        have s3_2_1a : u ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
        have s3_2_1b : f u ∈ Y := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
        -- 3.2.2. mun:in-union-left u := f(u), from 3.2.1
        have s3_2_2 : f u ∈ Y ∪ Z := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := Y) (Z := Z) (u := f u) s3_2_1b) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := Y) (Z := Z) (u := f u) s3_2_1b)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := Y) (Z := Z) (u := f u) s3_2_1b) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := Y) (Z := Z) (u := f u) s3_2_1b) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := Y) (Z := Z) (u := f u) s3_2_1b); parley_set_side)
        -- 3.2.3. def:preimage Z := Y ∪ Z, from 3.2.1, 3.2.2
        have s3_2_3 : u ∈ A ∩ f ⁻¹' (Y ∪ Z) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 3.2.4. def:preimage, from C4
        have s3_2_4a : u ∈ A := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).1; parley_set_side)
        have s3_2_4b : f u ∈ Z := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
        -- 3.2.5. mun:in-union-right u := f(u), from 3.2.4
        have s3_2_5 : f u ∈ Y ∪ Z := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := Y) (Z := Z) (u := f u) s3_2_4b) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := Y) (Z := Z) (u := f u) s3_2_4b)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := Y) (Z := Z) (u := f u) s3_2_4b) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := Y) (Z := Z) (u := f u) s3_2_4b) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := Y) (Z := Z) (u := f u) s3_2_4b); parley_set_side)
        -- 3.2.6. def:preimage Z := Y ∪ Z, from 3.2.4, 3.2.5
        have s3_2_6 : u ∈ A ∩ f ⁻¹' (Y ∪ Z) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
        all_goals parley_set_side
    all_goals exact s3_2
  -- 4. def:subset, from 3
  have s4 : A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z ⊆ A ∩ f ⁻¹' (Y ∪ Z) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) (Y := A ∩ f ⁻¹' (Y ∪ Z)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) (Y := A ∩ f ⁻¹' (Y ∪ Z)))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : A ∩ f ⁻¹' (Y ∪ Z) = A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) s2 s4) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) s2 s4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) s2 s4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) s2 s4) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) s2 s4); parley_set_side)
  all_goals exact s5

end Parley.Proofs.Hammack.PreimageOfUnion.PreimageOfUnion
