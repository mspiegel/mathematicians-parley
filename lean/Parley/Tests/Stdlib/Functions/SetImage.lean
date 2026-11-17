module

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
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/stdlib/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Functions.SetImage

theorem set_image {α β : Type*} [Nonempty α] [Nonempty β] (Y : Set α) (Z : Set β) (u : β) (E : α → β) (hH3 : Set.MapsTo E Y Z) (hH5 : u ∈ (fun s : α => E s) '' Y) :
    (∃ s ∈ Y, u = E s) := by
  -- 1. def:functions-set-image, from H5
  exact ((Parley.Items.Stdlib.Functions.def_set_image (E := E) (Y := Y) (u := u) (Z := Z) hH3)).mp hH5

end Parley.Tests.Stdlib.Functions.SetImage
