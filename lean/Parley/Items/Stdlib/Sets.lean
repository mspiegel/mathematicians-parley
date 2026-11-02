module

public import LeanBridges

/-! Written from corpus/stdlib/sets.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Sets

theorem def_subset {α : Type*} (X : Set α) (Y : Set α) :
    X ⊆ Y ↔ (∀ t ∈ X, t ∈ Y) :=
  Iff.rfl

theorem mun_in_union_left {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : u ∈ Y) :
    u ∈ Y ∪ Z :=
  Or.inl h1

theorem mun_in_union_right {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : u ∈ Z) :
    u ∈ Y ∪ Z :=
  Or.inr h1

theorem def_intersection {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∩ Z ↔ u ∈ Y ∧ u ∈ Z :=
  Iff.rfl

theorem def_union {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∪ Z ↔ u ∈ Y ∨ u ∈ Z :=
  Iff.rfl

theorem def_difference {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y \ Z ↔ u ∈ Y ∧ ¬ u ∈ Z :=
  Iff.rfl

theorem mun_subset_antisymmetric {α : Type*} (X : Set α) (Y : Set α) (h1 : X ⊆ Y) (h2 : Y ⊆ X) :
    X = Y :=
  Set.Subset.antisymm h1 h2

end Parley.Items.Stdlib.Sets
