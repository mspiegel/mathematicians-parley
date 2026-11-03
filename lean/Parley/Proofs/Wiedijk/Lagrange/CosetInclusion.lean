module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Lagrange.CosetWithin

/-! Written from proofs/wiedijk/lagrange.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lagrange.CosetInclusion

theorem coset_inclusion {G : Type*} [Group G] (H : Subgroup G) (hH2 : True) (a : G) (hH3 : a ∈ (Set.univ : Set G)) (x : G) (hH4 : x ∈ (a * ·) '' (H : Set G)) :
    (x * ·) '' (H : Set G) ⊆ (a * ·) '' (H : Set G) := by
  -- 1. mun:subgroup-within, from H2
  have s1 : (H : Set G) ⊆ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2); parley_set_side)
  -- 2. obtain h: def:coset u := x, g := a, from H2, H3, H4
  obtain ⟨h, s2a, s2b⟩ := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := a) (u := x) (H := H) hH2 hH3)).mp (by parley_set_side)
  -- 3. thm:coset-within g := a, from H2, H3
  have s3 : (a * ·) '' (H : Set G) ⊆ (Set.univ : Set G) := by first | exact (Parley.Proofs.Wiedijk.Lagrange.CosetWithin.coset_within (G := G) (H := H) hH2 (g := a) hH3) | exact ((Parley.Proofs.Wiedijk.Lagrange.CosetWithin.coset_within (G := G) (H := H) hH2 (g := a) hH3)).symm | simpa using (Parley.Proofs.Wiedijk.Lagrange.CosetWithin.coset_within (G := G) (H := H) hH2 (g := a) hH3) | exact_mod_cast (Parley.Proofs.Wiedijk.Lagrange.CosetWithin.coset_within (G := G) (H := H) hH2 (g := a) hH3) | (have h := (Parley.Proofs.Wiedijk.Lagrange.CosetWithin.coset_within (G := G) (H := H) hH2 (g := a) hH3); parley_set_side)
  -- 4. mun:in-subset, from H4, 3
  have s4 : x ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (a * ·) '' (H : Set G)) (Y := (Set.univ : Set G)) (u := x) s3 hH4) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (a * ·) '' (H : Set G)) (Y := (Set.univ : Set G)) (u := x) s3 hH4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (a * ·) '' (H : Set G)) (Y := (Set.univ : Set G)) (u := x) s3 hH4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (a * ·) '' (H : Set G)) (Y := (Set.univ : Set G)) (u := x) s3 hH4) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (a * ·) '' (H : Set G)) (Y := (Set.univ : Set G)) (u := x) s3 hH4); parley_set_side)
  -- 5. mun:in-subset, from 1, 2
  have s5 : h ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2a); parley_set_side)
  -- 6. proof
  have s6 : ∀ u ∈ (x * ·) '' (H : Set G), u ∈ (a * ·) '' (H : Set G) := by
    intro u hK1
    -- 6.1. obtain c: def:coset g := x, from H2, K1, 4
    obtain ⟨c, s6_1a, s6_1b⟩ := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := x) (u := u) (H := H) hH2 s4)).mp (by parley_set_side)
    -- 6.2. mun:in-subset, from 1, 6.1
    have s6_2 : c ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := c) s1 s6_1a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := c) s1 s6_1a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := c) s1 s6_1a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := c) s1 s6_1a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := c) s1 s6_1a); parley_set_side)
    -- 6.3. mun:subgroup-closed a := h, b := c, from H2, 2, 6.1
    have s6_3 : h * c ∈ (H : Set G) := by first | exact (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := h) s2a (b := c) s6_1a) | exact ((Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := h) s2a (b := c) s6_1a)).symm | simpa using (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := h) s2a (b := c) s6_1a) | exact_mod_cast (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := h) s2a (b := c) s6_1a) | (have h := (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) hH2 (a := h) s2a (b := c) s6_1a); parley_set_side)
    -- 6.4. calculation
    have s6_4 : u = a * (h * c) := by
      calc u = x * c := by parley_set_side
        _ = a * h * c := by parley_subst s2b
        _ = a * (h * c) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := h) (c := c) hH3 s5 s6_2) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := h) (c := c) hH3 s5 s6_2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := h) (c := c) hH3 s5 s6_2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := h) (c := c) hH3 s5 s6_2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := h) (c := c) hH3 s5 s6_2); parley_set_side)
    -- 6.5. def:coset g := a, from H2, H3, 6.3, 6.4
    have s6_5 : u ∈ (a * ·) '' (H : Set G) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := a) (u := u) (H := H) hH2 hH3)).mpr ⟨h * c, by parley_set_side, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := a) (u := u) (H := H) hH2 hH3)).mpr ⟨h * c, by parley_set_side, by parley_set_side⟩; parley_set_side)
    all_goals exact s6_5
  -- 7. def:subset, from 6
  have s7 : (x * ·) '' (H : Set G) ⊆ (a * ·) '' (H : Set G) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (x * ·) '' (H : Set G)) (Y := (a * ·) '' (H : Set G)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (x * ·) '' (H : Set G)) (Y := (a * ·) '' (H : Set G)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s7

end Parley.Proofs.Wiedijk.Lagrange.CosetInclusion
