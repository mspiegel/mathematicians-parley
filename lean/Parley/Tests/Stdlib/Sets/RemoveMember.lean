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
  have s1 : u ∈ Y \ ({a} : Set α) ↔ u ∈ Y ∧ ¬ u = a := by first | exact (Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := a) (u := u)) | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := a) (u := u))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := a) (u := u)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := a) (u := u)) | (have h := (Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := a) (u := u)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.RemoveMember
