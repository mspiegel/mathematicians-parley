module

public import SetTactics
public import Tactics
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
    have s1_1 : F t ∈ (∅ : Set α) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) hK1) | exact ((Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) hK1)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) hK1) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) hK1) | (have h := (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) hK1); parley_set_side)
    -- 1.2. inspection
    have s1_2 : ¬ F t ∈ (∅ : Set α) := by parley_set_side
    all_goals parley_set_side
  -- 2. def:subset, from 1
  have s2 : A ⊆ ∅ := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := ∅))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := ∅))).mpr (by parley_set_side); parley_set_side)
  -- 3. mun:subset-empty, from 2
  have s3 : A = ∅ := by first | exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A))).mp (by parley_set_side); parley_set_side)
  all_goals exact s3

end Parley.Proofs.Setmm.FunctionIntoEmpty.EmptyDomain
