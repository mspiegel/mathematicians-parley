module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/stdlib/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Functions.SetImage

theorem set_image {α : Type*} (Y : Set α) (Z : Set α) (u : α) (E : α → α) (hH3 : Set.MapsTo E Y Z) (hH5 : u ∈ (fun s : α => E s) '' Y) :
    (∃ s ∈ Y, u = E s) := by
  -- 1. def:functions-set-image, from H5
  have s1 : ∃ s ∈ Y, u = E s := by first | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := E) (Y := Y) (u := u) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_set_image (E := E) (Y := Y) (u := u) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_set_image (E := E) (Y := Y) (u := u) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_set_image (E := E) (Y := Y) (u := u) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := E) (Y := Y) (u := u) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Functions.SetImage
