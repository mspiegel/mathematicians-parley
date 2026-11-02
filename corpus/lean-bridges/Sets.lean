module

public import Mathlib
public import Counting

/-!
# Sets

What the library says of sets, each item said in
Lean as the build writes it.
-/

public section

namespace LeanBridges.Sets

/-- `mun:stdlib/sets/disjoint-empty`. -/
theorem disjoint_empty {α : Type*} (Y : Set α) (Z : Set α) (h1 : ∀ s ∈ Z, ¬ s ∈ Y) :
    Y ∩ Z = ∅ :=
  by ext s; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]; exact fun ⟨hy, hz⟩ => h1 s hz hy

/-- `mun:stdlib/sets/pair-subset`. -/
theorem pair_subset {α : Type*} (X : Set α) (a : α) (b : α) (h1 : a ∈ X) (h2 : b ∈ X) :
    {a, b} ⊆ X :=
  Set.insert_subset_iff.mpr ⟨h1, Set.singleton_subset_iff.mpr h2⟩

/-- `mun:stdlib/sets/disjoint-member`. -/
theorem disjoint_member {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : Y ∩ Z = ∅) (h2 : u ∈ Y) :
    ¬ u ∈ Z :=
  fun hz => by have h : u ∈ Y ∩ Z := ⟨h2, hz⟩; rw [h1] at h; exact h

end LeanBridges.Sets
