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

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.ElementOfItsCoset

theorem element_of_its_coset {G : Type*} [Group G] (H : Subgroup G) (g : G) (hH3 : g ∈ (Set.univ : Set G)) (h : G) (hH4 : h ∈ (H : Set G)) :
    g * h ∈ (g * ·) '' (H : Set G) := by
  -- 1. exhibit, from H4
  have s1 : ∃ k ∈ (H : Set G), g * h = g * k := ⟨h, hH4, rfl⟩
  -- 2. def:coset u := g·h, from H2, H3, 1
  exact ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := g * h) (H := H) (Set.mem_univ _))).mpr s1

end Parley.Proofs.Setmm.GroupCancellation.ElementOfItsCoset
