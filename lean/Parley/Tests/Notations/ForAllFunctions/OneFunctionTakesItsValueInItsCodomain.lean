module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Tests.Notations.ForAllFunctions.EveryFunctionTakesItsValuesInItsCodomain

/-! Written from tests/notations/for-all-functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.ForAllFunctions.OneFunctionTakesItsValueInItsCodomain

theorem one_function_takes_its_value_in_its_codomain {α : Type*} (X : Set α) (Y : Set α) (a : α) (hH3 : a ∈ X) (g : α → α) (hH4 : Set.MapsTo g X Y) :
    g a ∈ Y := by
  -- 1. thm:every-function-takes-its-values-in-its-codomain, from H3
  have s1 : ∀ f : α → α, Set.MapsTo f X Y → f a ∈ Y := by exact (Parley.Tests.Notations.ForAllFunctions.EveryFunctionTakesItsValuesInItsCodomain.every_function_takes_its_values_in_its_codomain (X := X) (Y := Y) (a := a) hH3)
  -- 2. instantiate f := g in line 1, from H4
  have s2 : g a ∈ Y := by first | exact (s1 g (by parley_set_side)) | exact ((s1 g (by parley_set_side))).symm | simpa using (s1 g (by parley_set_side)) | exact_mod_cast (s1 g (by parley_set_side)) | (have h := (s1 g (by parley_set_side)); parley_set_side)
  all_goals exact s2

end Parley.Tests.Notations.ForAllFunctions.OneFunctionTakesItsValueInItsCodomain
