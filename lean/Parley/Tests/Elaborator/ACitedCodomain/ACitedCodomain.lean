module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-cited-codomain.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedCodomain.ACitedCodomain

theorem a_cited_codomain {α : Type*} (A : Set α) (C : Set α) (B : α) (F : α → α) (hH4 : Set.MapsTo F A ({B} : Set α)) :
    (Set.MapsTo F A C ∧ Set.InjOn F A → (∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t)) := by
  -- 1. proof
  have s1 : Set.MapsTo F A C ∧ Set.InjOn F A → (∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t) := by
    intro hS
    -- 1.1. def:one-to-one f := F, from S
    have s1_1 : ∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t := by first | exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
    all_goals parley_set_side
  all_goals exact s1

end Parley.Tests.Elaborator.ACitedCodomain.ACitedCodomain
