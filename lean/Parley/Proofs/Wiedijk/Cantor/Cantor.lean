module

public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/cantor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Cantor.Cantor

theorem cantor {α : Type*} (A : Set α) (f : α → Set α) (hH2 : Set.MapsTo f A (𝒫 A)) :
    (∃ B ∈ 𝒫 A, ∀ x ∈ A, ¬ f x = B) := by
  set B : Set α := {x ∈ A | ¬ x ∈ f x} with hD1
  -- 1. mun:set-builder-subset, from D1
  have s1 : B ⊆ A := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun x : α => ¬ x ∈ f x)) (X := A))
  -- 2. proof
  have s2 : ∀ x ∈ A, ¬ f x = B := by
    intro x hK
    intro hS
    -- 2.1. contradiction
    have s2_1 : ¬ x ∈ B := by
      intro hS1
      -- 2.1.1. def:set-builder, from D1, S1
      have s2_1_1 : ¬ x ∈ f x := by
        try simp only [hD1] at *
        try push_cast at *
        first | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mp hS1 | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mp hS1).symm | simpa using ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mp hS1 | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mp hS1 | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mp hS1; parley_set_side)
      -- 2.1.2. substitute f(x) = B (S) into line 2.1.1
      have s2_1_2 : ¬ x ∈ B := by parley_subst_at hS s2_1_1
      exact s2_1_2 hS1
    -- 2.2. substitute f(x) = B (S) into line 2.1
    have s2_2 : ¬ x ∈ f x := by parley_subst_at hS s2_1
    -- 2.3. def:set-builder, from D1, K, 2.2
    have s2_3 : x ∈ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mpr (by parley_set_side); parley_set_side)
    exact s2_1 s2_3
  -- 3. exhibit, from 1, 2
  exact ⟨B, by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Cantor.Cantor
