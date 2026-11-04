module

public import Sets
public import Tactics

/-! Written from corpus/stdlib/sets.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Sets

theorem def_subset {α : Type*} (X : Set α) (Y : Set α) :
    X ⊆ Y ↔ (∀ t ∈ X, t ∈ Y) :=
  Iff.rfl

theorem def_set_builder {α : Type*} (P : α → Prop) (X : Set α) (u : α) :
    u ∈ {t ∈ X | P t} ↔ u ∈ X ∧ P u :=
  Set.mem_sep_iff

theorem mun_set_builder_subset {α : Type*} (P : α → Prop) (X : Set α) :
    {t ∈ X | P t} ⊆ X :=
  Set.sep_subset X P

theorem mun_subset_transitive {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : X ⊆ Y) (h2 : Y ⊆ Z) :
    X ⊆ Z :=
  h1.trans h2

theorem mun_subset_self {α : Type*} (X : Set α) :
    X ⊆ X :=
  Set.Subset.refl X

theorem def_powerset {α : Type*} (A : Set α) (S : Set α) :
    S ∈ 𝒫 A ↔ S ⊆ A :=
  Iff.rfl

theorem def_pair {α : Type*} (u : α) (w : α) (x : α) :
    x ∈ ({u, w} : Set α) ↔ x = u ∨ x = w :=
  Iff.rfl

theorem def_singleton {α : Type*} (a : α) (x : α) :
    x ∈ ({a} : Set α) ↔ x = a :=
  Iff.rfl

theorem mun_disjoint_empty {α : Type*} (Y : Set α) (Z : Set α) (h1 : ∀ s ∈ Z, ¬ s ∈ Y) :
    Y ∩ Z = ∅ :=
  LeanBridges.Sets.disjoint_empty Y Z h1

theorem mun_union_subset {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : X ⊆ Z) (h2 : Y ⊆ Z) :
    X ∪ Y ⊆ Z :=
  Set.union_subset h1 h2

theorem mun_in_union_left {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : u ∈ Y) :
    u ∈ Y ∪ Z :=
  Or.inl h1

theorem mun_in_union_right {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : u ∈ Z) :
    u ∈ Y ∪ Z :=
  Or.inr h1

theorem mun_difference_subset {α : Type*} (X : Set α) (Y : Set α) :
    X \ Y ⊆ X :=
  Set.diff_subset

theorem mun_difference_shrinks {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : Y ⊆ X) :
    Y \ Z ⊆ X \ Z :=
  Set.diff_subset_diff_left h1

theorem mun_singleton_subset {α : Type*} (X : Set α) (a : α) (h1 : a ∈ X) :
    ({a} : Set α) ⊆ X :=
  Set.singleton_subset_iff.mpr h1

theorem mun_pair_subset {α : Type*} (X : Set α) (a : α) (b : α) (h1 : a ∈ X) (h2 : b ∈ X) :
    ({a, b} : Set α) ⊆ X :=
  LeanBridges.Sets.pair_subset X a b h1 h2

theorem mun_powerset_monotone {α : Type*} (X : Set α) (Y : Set α) (h1 : Y ⊆ X) :
    𝒫 Y ⊆ 𝒫 X :=
  Set.powerset_mono.mpr h1

theorem def_intersection {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∩ Z ↔ u ∈ Y ∧ u ∈ Z :=
  Iff.rfl

theorem def_union {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∪ Z ↔ u ∈ Y ∨ u ∈ Z :=
  Iff.rfl

theorem mun_remove_member {α : Type*} (Y : Set α) (a : α) (u : α) :
    u ∈ Y \ ({a} : Set α) ↔ u ∈ Y ∧ ¬ u = a :=
  Set.mem_diff_singleton

theorem mun_intersection_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ Z = Z ∩ Y :=
  Set.inter_comm Y Z

theorem mun_union_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z = Z ∪ Y :=
  Set.union_comm Y Z

theorem mun_union_difference {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z \ Y = Y ∪ Z :=
  Set.union_diff_self

theorem mun_intersection_self {α : Type*} (Y : Set α) :
    Y ∩ Y = Y :=
  Set.inter_self Y

theorem mun_union_self {α : Type*} (Y : Set α) :
    Y ∪ Y = Y :=
  Set.union_self Y

theorem mun_union_empty {α : Type*} (Y : Set α) :
    Y ∪ ∅ = Y :=
  Set.union_empty Y

theorem mun_difference_self {α : Type*} (Y : Set α) :
    Y \ Y = ∅ :=
  Set.sdiff_self

theorem mun_subset_empty {α : Type*} (Y : Set α) :
    Y ⊆ ∅ ↔ Y = ∅ :=
  Set.subset_empty_iff

theorem def_difference {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y \ Z ↔ u ∈ Y ∧ ¬ u ∈ Z :=
  Iff.rfl

theorem mun_in_subset {α : Type*} (X : Set α) (Y : Set α) (u : α) (h1 : X ⊆ Y) (h2 : u ∈ X) :
    u ∈ Y :=
  h1 h2

theorem mun_disjoint_member {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : Y ∩ Z = ∅) (h2 : u ∈ Y) :
    ¬ u ∈ Z :=
  LeanBridges.Sets.disjoint_member Y Z u h1 h2

theorem mun_subset_antisymmetric {α : Type*} (X : Set α) (Y : Set α) (h1 : X ⊆ Y) (h2 : Y ⊆ X) :
    X = Y :=
  Set.Subset.antisymm h1 h2

end Parley.Items.Stdlib.Sets
