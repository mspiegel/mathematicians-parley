module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.NonemptyMember

theorem nonempty_member {α : Type*} (Y : Set α) (hH2 : ¬ Y = ∅) :
    (∃ a ∈ Y, True) := by
  -- 1. mun:sets-nonempty-member, from H2
  have s1 : ∃ a ∈ Y, True := by first | exact (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := Y) hH2) | exact ((Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := Y) hH2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := Y) hH2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := Y) hH2) | (have h := (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := Y) hH2); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.NonemptyMember
