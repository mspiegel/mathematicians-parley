module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Lagrange.CosetInclusion
public import Parley.Proofs.Wiedijk.Lagrange.CosetWithin

/-! Written from proofs/wiedijk/lagrange.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lagrange.CosetOfMember

set_option maxHeartbeats 400000 in
theorem coset_of_member {G : Type*} [Group G] (H : Subgroup G) (hH2 : True) (a : G) (hH3 : a ∈ (Set.univ : Set G)) (x : G) (hH4 : x ∈ (a * ·) '' (H : Set G)) :
    (x * ·) '' (H : Set G) = (a * ·) '' (H : Set G) := by
  -- 1. mun:subgroup-within, from H2
  have s1 : (H : Set G) ⊆ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H) hH2)
  -- 2. obtain h: def:coset u := x, g := a, from H2, H3, H4
  obtain ⟨h, s2a, s2b⟩ := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := a) (u := x) (H := H) hH2 hH3)).mp hH4
  -- 3. mun:in-subset, from 1, 2
  have s3 : h ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := h) s1 s2a)
  -- 4. mun:subgroup-inverse a := h, from H2, 2
  have s4 : h⁻¹ ∈ (H : Set G) := by exact (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) hH2 (a := h) s2a)
  -- 5. axi:group-inverse-closed a := h, from 3
  have s5 : h⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := h) s3)
  -- 6. axi:group-inverse a := h, from 3
  have s6 : h * h⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := h) s3)
  -- 7. calculation
  have s7 : a = x * h⁻¹ := by
    calc a = a * (1 : G) := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH3).symm
      _ = a * (h * h⁻¹) := by parley_subst s6
      _ = a * h * h⁻¹ := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := h) (c := h⁻¹) hH3 s3 s5).symm
      _ = x * h⁻¹ := by parley_subst s2b
  -- 8. thm:coset-within g := a, from H2, H3
  have s8 : (a * ·) '' (H : Set G) ⊆ (Set.univ : Set G) := by exact (Parley.Proofs.Wiedijk.Lagrange.CosetWithin.coset_within (G := G) (H := H) hH2 (g := a) hH3)
  -- 9. mun:in-subset, from H4, 8
  have s9 : x ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (a * ·) '' (H : Set G)) (Y := (Set.univ : Set G)) (u := x) s8 hH4)
  -- 10. def:coset u := a, g := x, from H2, 4, 7, 9
  have s10 : a ∈ (x * ·) '' (H : Set G) := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := x) (u := a) (H := H) hH2 s9)).mpr ⟨h⁻¹, by parley_set_side, by parley_set_side⟩
  -- 11. thm:coset-inclusion, from H2, H3, H4
  have s11 : (x * ·) '' (H : Set G) ⊆ (a * ·) '' (H : Set G) := by exact (Parley.Proofs.Wiedijk.Lagrange.CosetInclusion.coset_inclusion (G := G) (H := H) hH2 (a := a) hH3 (x := x) hH4)
  -- 12. thm:coset-inclusion a := x, x := a, from H2, 9, 10
  have s12 : (a * ·) '' (H : Set G) ⊆ (x * ·) '' (H : Set G) := by exact (Parley.Proofs.Wiedijk.Lagrange.CosetInclusion.coset_inclusion (G := G) (H := H) hH2 (a := x) s9 (x := a) s10)
  -- 13. mun:subset-antisymmetric, from 11, 12
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (x * ·) '' (H : Set G)) (Y := (a * ·) '' (H : Set G)) s11 s12)

end Parley.Proofs.Wiedijk.Lagrange.CosetOfMember
