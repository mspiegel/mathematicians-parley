module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups

/-! Written from tests/notations/groups.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Groups.ASubgroupTest

theorem a_subgroup_test {G : Type*} [Group G] (H : Subgroup G) (hH2 : True) (a : G) (hH3 : a ∈ (H : Set G)) (b : G) (hH4 : b ∈ (H : Set G)) :
    a * b⁻¹ ∈ (H : Set G) := by
  -- 1. mun:subgroup-inverse a := b, from H2, H4
  have s1 : b⁻¹ ∈ (H : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) (by parley_set_side) (a := b) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) (by parley_set_side) (a := b) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) (by parley_set_side) (a := b) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) (by parley_set_side) (a := b) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) (by parley_set_side) (a := b) (by parley_set_side)); parley_set_side)
  -- 2. mun:subgroup-closed b := b⁻¹, from H2, H3, 1
  have s2 : a * b⁻¹ ∈ (H : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) (by parley_set_side) (a := a) (by parley_set_side) (b := b⁻¹) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) (by parley_set_side) (a := a) (by parley_set_side) (b := b⁻¹) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) (by parley_set_side) (a := a) (by parley_set_side) (b := b⁻¹) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) (by parley_set_side) (a := a) (by parley_set_side) (b := b⁻¹) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) (by parley_set_side) (a := a) (by parley_set_side) (b := b⁻¹) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Tests.Notations.Groups.ASubgroupTest
