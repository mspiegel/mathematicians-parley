module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.Union

theorem union {α : Type*} (Y : Set α) (Z : Set α) (u : α) (hH4 : u ∈ Y ∪ Z) :
    (u ∈ Y ∨ u ∈ Z) := by
  -- 1. def:sets-union, from H4
  exact ((Parley.Items.Stdlib.Sets.def_union (Y := Y) (Z := Z) (u := u))).mp hH4

end Parley.Tests.Stdlib.Sets.Union
