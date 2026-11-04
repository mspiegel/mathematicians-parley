module

public import SetTactics
public import SubstTactics
public import Tactics
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
    all_goals parley_set_side
  -- 2. mun:function-into, from 1
  have s2 : Set.MapsTo F A ∅ := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := A) (Y := ∅) (by parley_set_side) s1) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := A) (Y := ∅) (by parley_set_side) s1)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := A) (Y := ∅) (by parley_set_side) s1) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := A) (Y := ∅) (by parley_set_side) s1) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := A) (Y := ∅) (by parley_set_side) s1); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Setmm.FunctionIntoEmpty.FunctionIntoEmpty
