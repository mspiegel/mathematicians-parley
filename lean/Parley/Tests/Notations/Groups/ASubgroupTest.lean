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
  have s1 : b⁻¹ ∈ (H : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) hH2 (a := b) hH4) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) hH2 (a := b) hH4)).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) hH2 (a := b) hH4) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) hH2 (a := b) hH4) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) hH2 (a := b) hH4); parley_set_side)
  -- 2. mun:subgroup-closed b := b⁻¹, from H2, H3, 1
  have s2 : a * b⁻¹ ∈ (H : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := a) hH3 (b := b⁻¹) s1) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := a) hH3 (b := b⁻¹) s1)).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := a) hH3 (b := b⁻¹) s1) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := a) hH3 (b := b⁻¹) s1) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := a) hH3 (b := b⁻¹) s1); parley_set_side)
  all_goals exact s2

end Parley.Tests.Notations.Groups.ASubgroupTest
