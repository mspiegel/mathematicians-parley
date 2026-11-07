module

public import Lean.Parser.Command
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Finite.Basic

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
    ({a, b} : Set α) ⊆ X :=
  Set.insert_subset_iff.mpr ⟨h1, Set.singleton_subset_iff.mpr h2⟩

/-- `mun:stdlib/sets/disjoint-member`. -/
theorem disjoint_member {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : Y ∩ Z = ∅) (h2 : u ∈ Y) :
    ¬ u ∈ Z :=
  fun hz => by have h : u ∈ Y ∩ Z := ⟨h2, hz⟩; rw [h1] at h; exact h

/-- An induction on the parts Y of a finite set X, starting at ∅: what
holds of ∅, and of Y ∪ {a} whenever of Y, for a member a of X not in Y,
holds of every part of X. The page's `induction on Y starting at ∅`,
written in the build's form of "for all Y ⊆ X", `∀ Y ∈ 𝒫 X`. -/
theorem subset_induction {α : Type*} {X : Set α} (hX : X.Finite) {P : Set α → Prop}
    (base : P ∅) (step : ∀ Y ∈ 𝒫 X, P Y → ∀ a ∈ X \ Y, P (Y ∪ {a})) :
    ∀ Y ∈ 𝒫 X, P Y := by
  intro Y hY
  have hYf : Y.Finite := hX.subset hY
  revert hY
  refine Set.Finite.induction_on (motive := fun Y _ => Y ⊆ X → P Y) Y hYf (fun _ => base) ?_
  intro a s has hs ih hsub
  have hsX : s ⊆ X := fun x hx => hsub (Set.mem_insert_of_mem a hx)
  have haX : a ∈ X := hsub (Set.mem_insert a s)
  have h := step s hsX (ih hsX) a ⟨haX, has⟩
  rwa [Set.union_singleton] at h

end LeanBridges.Sets
