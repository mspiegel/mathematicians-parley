module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/combinations.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Combinations.AddElementDisjoint

theorem add_element_disjoint {α : Type*} (Y : Set α) (a : α) (hH2 : ¬ a ∈ Y) (j : ℤ) :
    {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j} ∩ (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1} = ∅ := by
  set U : Set (Set α) := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j} with hD1
  set V : Set (Set α) := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1} with hD2
  -- 1. proof
  have s1 : ∀ T ∈ V, ¬ T ∪ ({a} : Set α) ∈ U := by
    intro T hK1
    intro hS1
    -- 1.1. mun:in-union-singleton
    have s1_1 : a ∈ T ∪ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := a))
    -- 1.2. def:part-builder u := T ∪ {a}, X := Y, from D1, S1
    have s1_2 : T ∪ ({a} : Set α) ⊆ Y := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T ∪ ({a} : Set α)))).mp (by parley_set_side)).1
    -- 1.3. mun:not-in-subset Y := T ∪ {a}, Z := Y, from H2, 1.2
    have s1_3 : ¬ a ∈ T ∪ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T ∪ ({a} : Set α)) (Z := Y) (a := a) hH2 s1_2)
    exact s1_3 s1_1
  -- 2. mun:added-elements-are-new Y := V, from 1
  have s2 : ∀ u ∈ (fun T : Set α => T ∪ ({a} : Set α)) '' V, ¬ u ∈ U := by exact (Parley.Items.Stdlib.Functions.mun_added_elements_are_new (Y := V) (Z := U) (a := a) s1)
  -- 3. mun:disjoint-empty, from D1, D2, 2
  try simp only [hD1, hD2] at ⊢
  try push_cast at ⊢
  exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (Z := (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1}) (by parley_set_side))

end Parley.Proofs.Wiedijk.Combinations.AddElementDisjoint
