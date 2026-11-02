module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/disjoint-power-set-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DisjointPowerSetDifference.DisjointPowerSetDifference

theorem disjoint_power_set_difference {α : Type*} (A : Set α) (B : Set α) (hH3 : A ∩ B = ∅) :
    𝒫 A \ 𝒫 B ⊆ 𝒫 (A \ B) := by
  -- 1. proof
  have s1 : ∀ t ∈ 𝒫 A \ 𝒫 B, t ∈ 𝒫 (A \ B) := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := 𝒫A, Z := 𝒫B, from K1
    have s1_1a : t ∈ 𝒫 A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    have s1_1b : ¬ t ∈ 𝒫 B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. def:powerset S := t, from 1.1
    have s1_2 : t ⊆ A := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp (by parley_set_side); parley_set_side)
    -- 1.3. proof
    have s1_3 : ∀ x ∈ t, x ∈ A \ B := by
      intro x hK2
      -- 1.3.1. mun:in-subset X := t, Y := A, u := x, from K2, 1.2
      have s1_3_1 : x ∈ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) (by parley_set_side) (by parley_set_side)); parley_set_side)
      -- 1.3.2. mun:disjoint-member Y := A, Z := B, u := x, from H3, 1.3.1
      have s1_3_2 : ¬ x ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := x) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := x) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := x) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := x) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := x) (by parley_set_side) (by parley_set_side)); parley_set_side)
      -- 1.3.3. def:difference u := x, Y := A, Z := B, from 1.3.1, 1.3.2
      have s1_3_3 : x ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := x))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := x))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    -- 1.4. def:subset, from 1.3
    have s1_4 : t ⊆ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A \ B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A \ B))).mpr (by parley_set_side); parley_set_side)
    -- 1.5. def:powerset S := t, A := A ∖ B, from 1.4
    have s1_5 : t ∈ 𝒫 (A \ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A \ B) (S := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A \ B) (S := t))).mpr (by parley_set_side); parley_set_side)
    all_goals parley_set_side
  -- 2. def:subset, from 1
  have s2 : 𝒫 A \ 𝒫 B ⊆ 𝒫 (A \ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 A \ 𝒫 B) (Y := 𝒫 (A \ B)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 A \ 𝒫 B) (Y := 𝒫 (A \ B)))).mpr (by parley_set_side); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Hammack.DisjointPowerSetDifference.DisjointPowerSetDifference
