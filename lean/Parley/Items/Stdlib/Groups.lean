module

public import Groups
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar

/-! Written from corpus/stdlib/groups.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Groups

theorem axi_group_closed {G : Type*} [Group G] (a : G) (b : G) (h1 : a ∈ (Set.univ : Set G)) (h2 : b ∈ (Set.univ : Set G)) :
    a * b ∈ (Set.univ : Set G) :=
  Set.mem_univ _

theorem axi_group_associative {G : Type*} [Group G] (a : G) (b : G) (c : G) (h1 : a ∈ (Set.univ : Set G)) (h2 : b ∈ (Set.univ : Set G)) (h3 : c ∈ (Set.univ : Set G)) :
    a * b * c = a * (b * c) :=
  mul_assoc a b c

theorem axi_group_identity {G : Type*} [Group G] (a : G) (h1 : a ∈ (Set.univ : Set G)) :
    a * (1 : G) = a :=
  mul_one a

theorem axi_group_identity_closed {G : Type*} [Group G] :
    (1 : G) ∈ (Set.univ : Set G) :=
  Set.mem_univ _

theorem axi_group_inverse {G : Type*} [Group G] (a : G) (h1 : a ∈ (Set.univ : Set G)) :
    a * a⁻¹ = (1 : G) :=
  mul_inv_cancel a

theorem axi_group_inverse_closed {G : Type*} [Group G] (a : G) (h1 : a ∈ (Set.univ : Set G)) :
    a⁻¹ ∈ (Set.univ : Set G) :=
  Set.mem_univ _

theorem thm_group_cancel {G : Type*} [Group G] (a : G) (b : G) (g : G) (h1 : a ∈ (Set.univ : Set G)) (h2 : b ∈ (Set.univ : Set G)) (h3 : g ∈ (Set.univ : Set G)) (h4 : g * a = g * b) :
    a = b :=
  mul_left_cancel h4

theorem mun_subgroup_within {G : Type*} [Group G] (H : Subgroup G) (h1 : True) :
    (H : Set G) ⊆ (Set.univ : Set G) :=
  Set.subset_univ _

theorem mun_subgroup_identity {G : Type*} [Group G] (H : Subgroup G) (h1 : True) :
    (1 : G) ∈ (H : Set G) :=
  H.one_mem

theorem mun_subgroup_closed {G : Type*} [Group G] (H : Subgroup G) (h1 : True) (a : G) (h2 : a ∈ (H : Set G)) (b : G) (h3 : b ∈ (H : Set G)) :
    a * b ∈ (H : Set G) :=
  H.mul_mem h2 h3

theorem mun_subgroup_inverse {G : Type*} [Group G] (H : Subgroup G) (h1 : True) (a : G) (h2 : a ∈ (H : Set G)) :
    a⁻¹ ∈ (H : Set G) :=
  H.inv_mem h2

theorem def_coset {G : Type*} [Group G] (g : G) (u : G) (H : Subgroup G) (h1 : True) (h2 : g ∈ (Set.univ : Set G)) :
    u ∈ (g * ·) '' (H : Set G) ↔ (∃ h ∈ (H : Set G), u = g * h) :=
  LeanBridges.Groups.coset g u H h1 h2

end Parley.Items.Stdlib.Groups
