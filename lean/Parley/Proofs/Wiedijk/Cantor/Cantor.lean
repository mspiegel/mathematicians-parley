module

public import InstanceTactics
public import SubstTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
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
    try simp only [hD1] at ⊢
    try push_cast at ⊢
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
        try simp only [hD1] at ⊢
        try push_cast at ⊢
        have hI : ¬ x ∈ f x := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mp hS1).2)
        exact hI
      -- 2.1.2. substitute f(x) = B (S) into line 2.1.1
      have s2_1_2 : ¬ x ∈ B := by parley_subst_at hS s2_1_1
      exact s2_1_2 hS1
    -- 2.2. substitute f(x) = B (S) into line 2.1
    have s2_2 : ¬ x ∈ f x := by parley_subst_at hS s2_1
    -- 2.3. def:set-builder, from D1, K, 2.2
    have s2_3 : x ∈ B := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => ¬ x ∈ f x)) (X := A) (u := x))).mpr ⟨hK, s2_2⟩
    exact s2_1 s2_3
  -- 3. exhibit, from 1, 2
  exact ⟨B, s1, s2⟩

end Parley.Proofs.Wiedijk.Cantor.Cantor
