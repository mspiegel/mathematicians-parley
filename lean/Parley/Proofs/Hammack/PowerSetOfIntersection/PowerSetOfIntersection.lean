module

public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/power-set-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PowerSetOfIntersection.PowerSetOfIntersection

theorem power_set_of_intersection {α : Type*} (A : Set α) (B : Set α) :
    𝒫 A ∩ 𝒫 B = 𝒫 (A ∩ B) := by
  -- 1. proof
  have s1 : ∀ t ∈ 𝒫 A ∩ 𝒫 B, t ∈ 𝒫 (A ∩ B) := by
    intro t hK1
    -- 1.1. def:intersection u := t, Y := 𝒫A, Z := 𝒫B, from K1
    have s1_1a : t ∈ 𝒫 A := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).1; parley_side)
    have s1_1b : t ∈ 𝒫 B := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_side)).2; parley_side)
    -- 1.2. def:powerset S := t, from 1.1
    have s1_2 : t ⊆ A := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_side); parley_side)
    -- 1.3. def:powerset S := t, A := B, from 1.1
    have s1_3 : t ⊆ B := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mp (by parley_side); parley_side)
    -- 1.4. proof
    have s1_4 : ∀ x ∈ t, x ∈ A ∩ B := by
      intro x hK2
      -- 1.4.1. mun:in-subset X := t, Y := A, u := x, from K2, 1.2
      have s1_4_1 : x ∈ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_side) (by parley_side)); parley_side)
      -- 1.4.2. mun:in-subset X := t, Y := B, u := x, from K2, 1.3
      have s1_4_2 : x ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := B) (u := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := B) (u := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := B) (u := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := B) (u := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := B) (u := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := B) (u := x) (by parley_side) (by parley_side)); parley_side)
      -- 1.4.3. def:intersection u := x, Y := A, Z := B, from 1.4.1, 1.4.2
      have s1_4_3 : x ∈ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 1.5. def:subset, from 1.4
    have s1_5 : t ⊆ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A ∩ B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A ∩ B))).mpr (by parley_side); parley_side)
    -- 1.6. def:powerset S := t, A := A ∩ B, from 1.5
    have s1_6 : t ∈ 𝒫 (A ∩ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : 𝒫 A ∩ 𝒫 B ⊆ 𝒫 (A ∩ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)))).mpr (by parley_side); parley_side)
  -- 3. proof
  have s3 : ∀ t ∈ 𝒫 (A ∩ B), t ∈ 𝒫 A ∩ 𝒫 B := by
    intro t hK3
    -- 3.1. def:powerset S := t, A := A ∩ B, from K3
    have s3_1 : t ⊆ A ∩ B := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mp (by parley_side); parley_side)
    -- 3.2. proof
    have s3_2 : ∀ x ∈ t, x ∈ A := by
      intro x hK4
      -- 3.2.1. mun:in-subset X := t, Y := A ∩ B, u := x, from K4, 3.1
      have s3_2_1 : x ∈ A ∩ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)); parley_side)
      -- 3.2.2. def:intersection u := x, Y := A, Z := B, from 3.2.1
      have s3_2_2 : x ∈ A := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side); parley_side)
      all_goals parley_side
    -- 3.3. proof
    have s3_3 : ∀ x ∈ t, x ∈ B := by
      intro x hK5
      -- 3.3.1. mun:in-subset X := t, Y := A ∩ B, u := x, from K5, 3.1
      have s3_3_1 : x ∈ A ∩ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) (by parley_side) (by parley_side)); parley_side)
      -- 3.3.2. def:intersection u := x, Y := A, Z := B, from 3.3.1
      have s3_3_2 : x ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp (by parley_side); parley_side)
      all_goals parley_side
    -- 3.4. def:subset, from 3.2
    have s3_4 : t ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A))).mpr (by parley_side); parley_side)
    -- 3.5. def:subset, from 3.3
    have s3_5 : t ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := B))).mpr (by parley_side); parley_side)
    -- 3.6. def:powerset S := t, from 3.4
    have s3_6 : t ∈ 𝒫 A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mpr (by parley_side); parley_side)
    -- 3.7. def:powerset S := t, A := B, from 3.5
    have s3_7 : t ∈ 𝒫 B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mpr (by parley_side); parley_side)
    -- 3.8. def:intersection u := t, Y := 𝒫A, Z := 𝒫B, from 3.6, 3.7
    have s3_8 : t ∈ 𝒫 A ∩ 𝒫 B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 4. def:subset, from 3
  have s4 : 𝒫 (A ∩ B) ⊆ 𝒫 A ∩ 𝒫 B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 (A ∩ B)) (Y := 𝒫 A ∩ 𝒫 B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 (A ∩ B)) (Y := 𝒫 A ∩ 𝒫 B))).mpr (by parley_side); parley_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : 𝒫 A ∩ 𝒫 B = 𝒫 (A ∩ B) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.PowerSetOfIntersection.PowerSetOfIntersection
