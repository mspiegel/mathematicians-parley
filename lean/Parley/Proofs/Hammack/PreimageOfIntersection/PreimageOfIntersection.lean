module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/preimage-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfIntersection.PreimageOfIntersection

set_option maxHeartbeats 400000 in
theorem preimage_of_intersection {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (Y : Set α) (hH4 : Y ⊆ B) (Z : Set α) (hH5 : Z ⊆ B) :
    A ∩ f ⁻¹' (Y ∩ Z) = (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z) := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ f ⁻¹' (Y ∩ Z), u ∈ (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z) := by
    intro u hK1
    -- 1.1. def:preimage Z := Y ∩ Z, from K1
    have s1_1a : u ∈ A := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∩ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK1).1
    have s1_1b : f u ∈ Y ∩ Z := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∩ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK1).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∩ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK1).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∩ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK1).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∩ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK1).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∩ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp hK1).2; parley_set_side)
    -- 1.2. def:intersection u := f(u), from 1.1
    have s1_2a : f u ∈ Y := (((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := f u))).mp s1_1b).1
    have s1_2b : f u ∈ Z := (((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := f u))).mp s1_1b).2
    -- 1.3. def:preimage Z := Y, from 1.1, 1.2
    have s1_3 : u ∈ A ∩ f ⁻¹' Y := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side)
    -- 1.4. def:preimage, from 1.1, 1.2
    have s1_4 : u ∈ A ∩ f ⁻¹' Z := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side)
    -- 1.5. def:intersection Y := f⁻¹[Y], Z := f⁻¹[Z], from 1.3, 1.4
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mpr (by parley_set_side)
  -- 2. def:subset, from 1
  have s2 : A ∩ f ⁻¹' (Y ∩ Z) ⊆ (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z) := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (Y ∩ Z)) (Y := (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z)))).mpr s1
  -- 3. proof
  have s3 : ∀ u ∈ (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z), u ∈ A ∩ f ⁻¹' (Y ∩ Z) := by
    intro u hK2
    -- 3.1. def:intersection Y := f⁻¹[Y], Z := f⁻¹[Z], from K2
    have s3_1a : u ∈ A ∩ f ⁻¹' Y := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp hK2).1
    have s3_1b : u ∈ A ∩ f ⁻¹' Z := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp hK2).2
    -- 3.2. def:preimage Z := Y, from 3.1
    have s3_2a : u ∈ A := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1a).1
    have s3_2b : f u ∈ Y := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1a).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1a).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1a).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1a).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1a).2; parley_set_side)
    -- 3.3. def:preimage, from 3.1
    have s3_3 : f u ∈ Z := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1b).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1b).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1b).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1b).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mp s3_1b).2; parley_set_side)
    -- 3.4. def:intersection u := f(u), from 3.2, 3.3
    have s3_4 : f u ∈ Y ∩ Z := ((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := f u))).mpr (by parley_set_side)
    -- 3.5. def:preimage Z := Y ∩ Z, from 3.2, 3.4
    exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∩ Z) (f := f) (u := u) (W := Set.univ) (by parley_set_side))).mpr (by parley_set_side)
  -- 4. def:subset, from 3
  have s4 : (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z) ⊆ A ∩ f ⁻¹' (Y ∩ Z) := ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z)) (Y := A ∩ f ⁻¹' (Y ∩ Z)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (Y ∩ Z)) (Y := (A ∩ f ⁻¹' Y) ∩ (A ∩ f ⁻¹' Z)) s2 s4)

end Parley.Proofs.Hammack.PreimageOfIntersection.PreimageOfIntersection
