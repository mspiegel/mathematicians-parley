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

theorem a_type_a_line_states_for_a_theorem {α : Type*} (A : Set α) (F : α → α) (hH3 : Set.MapsTo F A ∅) :
    (∀ t ∈ A, F t ∈ (∅ : Set α)) := by
  -- 1. thm:into-the-empty-set, from H3
  exact (Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet.into_the_empty_set (A := A) (F := F) hH3)

end Parley.Tests.Elaborator.ATypeALineStates.ATypeALineStatesForATheorem
