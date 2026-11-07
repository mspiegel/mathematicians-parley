module

public import ArithTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
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
    by_contra hc_hS1
    have hS1 : T ∪ ({a} : Set α) ∈ U := by parley_suppose hc_hS1
    -- 1.1. mun:in-union-singleton
    have s1_1 : a ∈ T ∪ ({a} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := a)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := a))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := a)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := a)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := a)); parley_set_side)
    -- 1.2. def:part-builder u := T ∪ {a}, X := Y, from D1, S1
    have s1_2 : T ∪ ({a} : Set α) ⊆ Y := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T ∪ ({a} : Set α)))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T ∪ ({a} : Set α)))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T ∪ ({a} : Set α)))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T ∪ ({a} : Set α)))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T ∪ ({a} : Set α)))).mp (by parley_set_side)).1; parley_set_side)
    -- 1.3. mun:not-in-subset Y := T ∪ {a}, Z := Y, from H2, 1.2
    have s1_3 : ¬ a ∈ T ∪ ({a} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T ∪ ({a} : Set α)) (Z := Y) (a := a) hH2 s1_2) | exact ((Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T ∪ ({a} : Set α)) (Z := Y) (a := a) hH2 s1_2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T ∪ ({a} : Set α)) (Z := Y) (a := a) hH2 s1_2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T ∪ ({a} : Set α)) (Z := Y) (a := a) hH2 s1_2) | (have h := (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T ∪ ({a} : Set α)) (Z := Y) (a := a) hH2 s1_2); parley_set_side)
    all_goals parley_set_side
  -- 2. mun:added-elements-are-new Y := V, from 1
  have s2 : ∀ u ∈ (fun T : Set α => T ∪ ({a} : Set α)) '' V, ¬ u ∈ U := by first | exact (Parley.Items.Stdlib.Functions.mun_added_elements_are_new (Y := V) (Z := U) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_added_elements_are_new (Y := V) (Z := U) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_added_elements_are_new (Y := V) (Z := U) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_added_elements_are_new (Y := V) (Z := U) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_added_elements_are_new (Y := V) (Z := U) (a := a) (by parley_set_side)); parley_set_side)
  -- 3. mun:disjoint-empty, from D1, D2, 2
  have s3 : {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j} ∩ (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1} = ∅ := by
    try simp only [hD1, hD2] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (Z := (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1}) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (Z := (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1}) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (Z := (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1}) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (Z := (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1}) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (Z := (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j - 1}) (by parley_set_side)); parley_set_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.Combinations.AddElementDisjoint
