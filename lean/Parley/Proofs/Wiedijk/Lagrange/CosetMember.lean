module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups

/-! Written from proofs/wiedijk/lagrange.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lagrange.CosetMember

theorem coset_member {G : Type*} [Group G] (H : Subgroup G) (hH2 : True) (g : G) (hH3 : g ∈ (Set.univ : Set G)) :
    g ∈ (g * ·) '' (H : Set G) := by
  -- 1. mun:subgroup-identity, from H2
  have s1 : (1 : G) ∈ (H : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) (by parley_set_side)); parley_set_side)
  -- 2. axi:group-identity a := g, from H3
  have s2 : g * (1 : G) = g := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) (by parley_set_side)); parley_set_side)
  -- 3. def:coset u := g, from H2, H3, 1, 2
  have s3 : g ∈ (g * ·) '' (H : Set G) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := g) (H := H) (by parley_set_side) (by parley_set_side))).mpr ⟨(1 : G), by parley_set_side, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := g) (H := H) (by parley_set_side) (by parley_set_side))).mpr ⟨(1 : G), by parley_set_side, by parley_set_side⟩; parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Wiedijk.Lagrange.CosetMember
