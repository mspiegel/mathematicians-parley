module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/function-into-empty.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FunctionIntoEmpty.FunctionIntoEmpty

theorem function_into_empty {α : Type*} (A : Set α) (F : α → α) (hH2 : True) (hH3 : A = ∅) :
    Set.MapsTo F A ∅ := by
  -- 1. proof
  have s1 : ∀ x ∈ A, F x ∈ (∅ : Set α) := by
    intro x hK1
    -- 1.1. substitute A = ∅ (H3) into K1
    have s1_1 : x ∈ (∅ : Set α) := by parley_subst_at hH3 hK1
    -- 1.2. inspection
    have s1_2 : ¬ x ∈ (∅ : Set α) := by parley_set_side
    exact absurd s1_1 s1_2
  -- 2. mun:function-into, from 1
  exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := A) (Y := ∅) (by parley_set_side) s1)

end Parley.Proofs.Setmm.FunctionIntoEmpty.FunctionIntoEmpty
