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

namespace Parley.Tests.Stdlib.Sets.NonemptyMember

theorem nonempty_member {α : Type*} (Y : Set α) (hH2 : ¬ Y = ∅) :
    (∃ a ∈ Y, True) := by
  -- 1. mun:sets-nonempty-member, from H2
  exact (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := Y) hH2)

end Parley.Tests.Stdlib.Sets.NonemptyMember
