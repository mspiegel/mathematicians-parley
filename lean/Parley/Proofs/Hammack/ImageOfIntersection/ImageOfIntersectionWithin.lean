module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfIntersection.ImageOfIntersectionWithin

set_option maxHeartbeats 400000 in
theorem image_of_intersection_within {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (W : Set α) (hH4 : W ⊆ A) (X : Set α) (hH5 : X ⊆ A) :
    f '' (A ∩ (W ∩ X)) ⊆ f '' (A ∩ W) ∩ f '' (A ∩ X) := by
  -- 1. proof
  have s1 : ∀ s ∈ W ∩ X, s ∈ A := by
    intro s hK1
    -- 1.1. def:intersection u := s, Y := W, Z := X, from K1
    have s1_1a : s ∈ W := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1; parley_set_side)
    have s1_1b : s ∈ X := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. mun:in-subset X := W, Y := A, u := s, from H4, 1.1
    have s1_2 : s ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := A) (u := s) hH4 s1_1a)
    all_goals exact s1_2
  -- 2. def:subset, from 1
  have s2 : W ∩ X ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := W ∩ X) (Y := A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := W ∩ X) (Y := A))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ y ∈ f '' (A ∩ (W ∩ X)), y ∈ f '' (A ∩ W) ∩ f '' (A ∩ X) := by
    intro y hK2
    -- 3.1. obtain s: def:image u := y, Y := W ∩ X, from K2, 2
    obtain ⟨s, s3_1a, s3_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := W ∩ X) (f := f) (u := y) (W := Set.univ) s2 (by parley_set_side))).mp (by parley_set_side)
    -- 3.2. def:intersection u := s, Y := W, Z := X, from 3.1
    have s3_2a : s ∈ W := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).1; parley_set_side)
    have s3_2b : s ∈ X := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).2; parley_set_side)
    -- 3.3. mun:value-in-image Y := W, from H4, 3.2
    have s3_3 : f s ∈ f '' (A ∩ W) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := Set.univ) hH4 s3_2a (by parley_set_side))
    -- 3.4. mun:value-in-image Y := X, from H5, 3.2
    have s3_4 : f s ∈ f '' (A ∩ X) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := Set.univ) hH5 s3_2b (by parley_set_side))
    -- 3.5. substitute y = f(s) (line 3.1) into line 3.3
    have s3_5 : y ∈ f '' (A ∩ W) := by parley_subst_at s3_1b s3_3
    -- 3.6. substitute y = f(s) (line 3.1) into line 3.4
    have s3_6 : y ∈ f '' (A ∩ X) := by parley_subst_at s3_1b s3_4
    -- 3.7. def:intersection u := y, Y := f[W], Z := f[X], from 3.5, 3.6
    have s3_7 : y ∈ f '' (A ∩ W) ∩ f '' (A ∩ X) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := f '' (A ∩ W)) (Z := f '' (A ∩ X)) (u := y))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := f '' (A ∩ W)) (Z := f '' (A ∩ X)) (u := y))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s3_7
  -- 4. def:subset, from 3
  have s4 : f '' (A ∩ (W ∩ X)) ⊆ f '' (A ∩ W) ∩ f '' (A ∩ X) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (A ∩ (W ∩ X))) (Y := f '' (A ∩ W) ∩ f '' (A ∩ X)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (A ∩ (W ∩ X))) (Y := f '' (A ∩ W) ∩ f '' (A ∩ X)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s4

end Parley.Proofs.Hammack.ImageOfIntersection.ImageOfIntersectionWithin
