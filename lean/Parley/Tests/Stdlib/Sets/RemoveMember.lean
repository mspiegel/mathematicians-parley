module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.RemoveMember

theorem remove_member {α : Type*} (Y : Set α) (a : α) (u : α) :
    (u ∈ Y \ ({a} : Set α) ↔ u ∈ Y ∧ ¬ u = a) := by
  -- 1. mun:sets-remove-member
  exact (Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := a) (u := u))

end Parley.Tests.Stdlib.Sets.RemoveMember
