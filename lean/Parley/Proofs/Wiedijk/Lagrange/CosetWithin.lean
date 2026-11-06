module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/lagrange.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lagrange.CosetWithin

theorem coset_within {G : Type*} [Group G] (H : Subgroup G) (hH2 : True) (g : G) (hH3 : g ∈ (Set.univ : Set G)) :
    (g * ·) '' (H : Set G) ⊆ (Set.univ : Set G) := by
  -- 1. mun:subgroup-within, from H2
  have s1 : (H : Set G) ⊆ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2); parley_set_side)
  -- 2. proof
  have s2 : ∀ u ∈ (g * ·) '' (H : Set G), u ∈ (Set.univ : Set G) := by
    intro u hK1
    -- 2.1. obtain h: def:coset, from H2, H3, K1
    obtain ⟨h, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := u) (H := H) hH2 hH3)).mp (by parley_set_side)
    -- 2.2. mun:in-subset, from 1, 2.1
    have s2_2 : h ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2_1a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2_1a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2_1a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2_1a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2_1a); parley_set_side)
    -- 2.3. axi:group-closed a := g, b := h, from H3, 2.2
    have s2_3 : g * h ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := g) (b := h) hH3 s2_2) | exact ((Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := g) (b := h) hH3 s2_2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := g) (b := h) hH3 s2_2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := g) (b := h) hH3 s2_2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := g) (b := h) hH3 s2_2); parley_set_side)
    -- 2.4. substitute u = g·h (line 2.1) into line 2.3
    have s2_4 : u ∈ (Set.univ : Set G) := by parley_subst_at s2_1b s2_3
    all_goals exact s2_4
  -- 3. def:subset, from 2
  have s3 : (g * ·) '' (H : Set G) ⊆ (Set.univ : Set G) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (g * ·) '' (H : Set G)) (Y := (Set.univ : Set G)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (g * ·) '' (H : Set G)) (Y := (Set.univ : Set G)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.Lagrange.CosetWithin
