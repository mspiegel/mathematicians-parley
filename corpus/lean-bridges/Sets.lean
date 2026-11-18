module

public import Lean.Parser.Command
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Int.Interval

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

/-- A set each member of which is f(i) for some i in a range of integers is
finite: the edges of a walk that crosses every edge, each some e(i). -/
theorem finite_of_covered_by_range {α : Type*} {A : Set α} (a b : ℤ) (f : ℤ → α)
    (h : ∀ x ∈ A, ∃ i : ℤ, i ∈ Finset.Icc a b ∧ x = f i) : A.Finite :=
  ((Finset.Icc a b).finite_toSet.image f).subset fun x hx => by
    obtain ⟨i, hi, rfl⟩ := h x hx
    exact ⟨i, hi, rfl⟩

/-! What a property keeps of a set listed in full, member by member: what
`inspection` reads of {x ∈ E : P(x)} where E = {b₁, …, bₙ}. -/

/-- A listed member the property holds of is kept. -/
theorem sep_insert_of {α : Type*} {s : Set α} {p : α → Prop} {a : α} (h : p a) :
    {x ∈ insert a s | p x} = insert a {x ∈ s | p x} := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]; constructor
  · rintro ⟨rfl | hx, hp⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hx, hp⟩
  · rintro (rfl | ⟨hx, hp⟩)
    · exact ⟨Or.inl rfl, h⟩
    · exact ⟨Or.inr hx, hp⟩

/-- A listed member the property does not hold of is left out. -/
theorem sep_insert_of_not {α : Type*} {s : Set α} {p : α → Prop} {a : α} (h : ¬ p a) :
    {x ∈ insert a s | p x} = {x ∈ s | p x} := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]; constructor
  · rintro ⟨rfl | hx, hp⟩
    · exact absurd hp h
    · exact ⟨hx, hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨Or.inr hx, hp⟩

/-- The last listed member, kept. -/
theorem sep_singleton_of {α : Type*} {p : α → Prop} {a : α} (h : p a) :
    {x ∈ ({a} : Set α) | p x} = {a} := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]; constructor
  · exact fun ⟨hx, _⟩ => hx
  · rintro rfl; exact ⟨rfl, h⟩

/-- The last listed member, left out. -/
theorem sep_singleton_of_not {α : Type*} {p : α → Prop} {a : α} (h : ¬ p a) :
    {x ∈ ({a} : Set α) | p x} = ∅ := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl; exact h

end LeanBridges.Sets
