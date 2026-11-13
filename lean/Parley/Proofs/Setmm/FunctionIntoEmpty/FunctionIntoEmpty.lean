module

public import SubstTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Basic
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
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/function-into-empty.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FunctionIntoEmpty.FunctionIntoEmpty

theorem function_into_empty {α : Type*} (A : Set α) (F : α → α) (hH3 : A = ∅) :
    Set.MapsTo F A ∅ := by
  -- 1. proof
  have s1 : ∀ x ∈ A, F x ∈ (∅ : Set α) := by
    intro x hK1
    -- 1.1. substitute A = ∅ (H3) into K1
    have s1_1 : x ∈ (∅ : Set α) := by parley_subst_at hH3 hK1
    -- 1.2. inspection
    have s1_2 : ¬ x ∈ (∅ : Set α) := Set.notMem_empty _
    exact absurd s1_1 s1_2
  -- 2. mun:function-into, from 1
  exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := A) (Y := ∅) s1)

end Parley.Proofs.Setmm.FunctionIntoEmpty.FunctionIntoEmpty
