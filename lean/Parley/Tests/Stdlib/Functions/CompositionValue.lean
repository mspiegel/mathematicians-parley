module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/stdlib/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Functions.CompositionValue

theorem composition_value {α : Type*} (A : Set α) (B : Set α) (C : Set α) (f : α → α) (hH4 : Set.MapsTo f A B) (g : α → α) (hH5 : Set.MapsTo g B C) (a : α) (hH6 : a ∈ A) :
    (g ∘ f) a = g (f a) := by
  -- 1. mun:functions-composition-value x := a, from H6
  have s1 : (g ∘ f) a = g (f a) := by first | exact (Parley.Items.Stdlib.Functions.mun_composition_value (Y := B) (X := A) (f := f) (g := g) (x := a) (W := Set.univ) hH6 (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_composition_value (Y := B) (X := A) (f := f) (g := g) (x := a) (W := Set.univ) hH6 (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_composition_value (Y := B) (X := A) (f := f) (g := g) (x := a) (W := Set.univ) hH6 (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_composition_value (Y := B) (X := A) (f := f) (g := g) (x := a) (W := Set.univ) hH6 (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_composition_value (Y := B) (X := A) (f := f) (g := g) (x := a) (W := Set.univ) hH6 (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Functions.CompositionValue
