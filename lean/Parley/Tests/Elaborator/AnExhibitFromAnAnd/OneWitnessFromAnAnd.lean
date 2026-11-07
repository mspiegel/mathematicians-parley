module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/an-exhibit-from-an-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitFromAnAnd.OneWitnessFromAnAnd

theorem one_witness_from_an_and {α : Type*} (V : Set α) (b : α) (hH2 : b ∈ V) (a : α) (hH3 : a ∈ V \ ({b} : Set α)) :
    (∃ x ∈ V, ¬ x = b) := by
  -- 1. mun:remove-member u := a, Y := V, a := b, from H3
  have s1 : a ∈ V ∧ ¬ a = b := by first | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp (by parley_set_side); parley_set_side)
  -- 2. exhibit, from 1
  have s2 : ∃ x ∈ V, ¬ x = b := ⟨a, by parley_set_side, by parley_set_side⟩
  all_goals exact s2

end Parley.Tests.Elaborator.AnExhibitFromAnAnd.OneWitnessFromAnAnd
