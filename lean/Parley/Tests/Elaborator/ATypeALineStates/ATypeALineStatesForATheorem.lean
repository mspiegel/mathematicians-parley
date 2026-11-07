module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet

/-! Written from tests/elaborator/a-type-a-line-states.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATypeALineStates.ATypeALineStatesForATheorem

theorem a_type_a_line_states_for_a_theorem {α : Type*} (A : Set α) (F : α → α) (hH2 : True) (hH3 : Set.MapsTo F A ∅) :
    (∀ t ∈ A, F t ∈ (∅ : Set α)) := by
  -- 1. thm:into-the-empty-set, from H3
  have s1 : ∀ t ∈ A, F t ∈ (∅ : Set α) := by exact (Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet.into_the_empty_set (A := A) (F := F) (by parley_set_side))
  all_goals exact s1

end Parley.Tests.Elaborator.ATypeALineStates.ATypeALineStatesForATheorem
