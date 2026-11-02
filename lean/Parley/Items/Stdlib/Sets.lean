module

public import LeanBridges

/-! Written from corpus/stdlib/sets.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Sets

theorem def_subset {α : Type*} (X : Set α) (Y : Set α) :
    X ⊆ Y ↔ (∀ t ∈ X, t ∈ Y) :=
  Iff.rfl

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

theorem mun_singleton_subset {α : Type*} (X : Set α) (a : α) (h1 : a ∈ X) :
    ({a} : Set α) ⊆ X :=
  Set.singleton_subset_iff.mpr h1

theorem mun_pair_subset {α : Type*} (X : Set α) (a : α) (b : α) (h1 : a ∈ X) (h2 : b ∈ X) :
    ({a, b} : Set α) ⊆ X :=
  LeanBridges.Sets.pair_subset X a b h1 h2

theorem def_intersection {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∩ Z ↔ u ∈ Y ∧ u ∈ Z :=
  Iff.rfl

theorem def_union {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∪ Z ↔ u ∈ Y ∨ u ∈ Z :=
  Iff.rfl

theorem mun_intersection_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ Z = Z ∩ Y :=
  Set.inter_comm Y Z

theorem mun_union_difference {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z \ Y = Y ∪ Z :=
  Set.union_diff_self

theorem mun_intersection_self {α : Type*} (Y : Set α) :
    Y ∩ Y = Y :=
  Set.inter_self Y

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
