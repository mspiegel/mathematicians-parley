module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups

/-! Written from proofs/wiedijk/lagrange.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lagrange.CosetMember

theorem coset_member {G : Type*} [Group G] (H : Subgroup G) (hH2 : True) (g : G) (hH3 : g ∈ (Set.univ : Set G)) :
    g ∈ (g * ·) '' (H : Set G) := by
  -- 1. mun:subgroup-identity, from H2
  have s1 : (1 : G) ∈ (H : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) hH2) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) hH2) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_identity (G := G) (H := H) hH2); parley_set_side)
  -- 2. axi:group-identity a := g, from H3
  have s2 : g * (1 : G) = g := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) hH3) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) hH3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) hH3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) hH3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := g) hH3); parley_set_side)
  -- 3. def:coset u := g, from H2, H3, 1, 2
  have s3 : g ∈ (g * ·) '' (H : Set G) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := g) (H := H) hH2 hH3)).mpr ⟨(1 : G), by parley_set_side, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := g) (H := H) hH2 hH3)).mpr ⟨(1 : G), by parley_set_side, by parley_set_side⟩; parley_set_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.Lagrange.CosetMember
