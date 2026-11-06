module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-define-cited-as-a-step.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineCitedAsAStep.ADefineCitedAsAStep

theorem a_define_cited_as_a_step {α : Type*} (A : Set α) (F : α → α) (hH2 : Set.MapsTo F A A) (h : α → α) (hD1 : ∀ x : α, x ∈ A → h x = F x) :
    True := by
  -- 1. D1
  all_goals parley_set_side

end Parley.Tests.Elaborator.ADefineCitedAsAStep.ADefineCitedAsAStep
