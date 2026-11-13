module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/function-into-empty.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FunctionIntoEmpty.EmptyDomain

theorem empty_domain {α : Type*} (A : Set α) (F : α → α) (hH2 : Set.MapsTo F A ∅) :
    A = ∅ := by
  -- 1. proof
  have s1 : ∀ t ∈ A, t ∈ (∅ : Set α) := by
    intro t hK1
    -- 1.1. mun:function-value f := F, from K1
    have s1_1 : F t ∈ (∅ : Set α) := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) hK1 hH2)
    -- 1.2. inspection
    have s1_2 : ¬ F t ∈ (∅ : Set α) := Set.notMem_empty _
    exact absurd s1_1 s1_2
  -- 2. def:subset, from 1
  have s2 : A ⊆ ∅ := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := ∅))).mpr s1
  -- 3. mun:subset-empty, from 2
  exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A))).mp s2

end Parley.Proofs.Setmm.FunctionIntoEmpty.EmptyDomain
