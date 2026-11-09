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

namespace Parley.Tests.Elaborator.AnExhibitFromAnAnd.TwoWitnessesFromAnAnd

theorem two_witnesses_from_an_and {α : Type*} (V : Set α) (b : α) (hH2 : b ∈ V) (a : α) (hH3 : a ∈ V \ ({b} : Set α)) :
    (∃ x ∈ V, ∃ y ∈ V, ¬ x = y) := by
  -- 1. mun:remove-member u := a, Y := V, a := b, from H3
  have s1 : a ∈ V ∧ ¬ a = b := by exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp hH3
  -- 2. exhibit, from H2, 1
  exact ⟨b, hH2, a, s1.1, Ne.symm s1.2⟩

end Parley.Tests.Elaborator.AnExhibitFromAnAnd.TwoWitnessesFromAnAnd
