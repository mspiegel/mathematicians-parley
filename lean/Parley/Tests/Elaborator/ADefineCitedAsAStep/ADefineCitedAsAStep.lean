module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-define-cited-as-a-step.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineCitedAsAStep.ADefineCitedAsAStep

theorem a_define_cited_as_a_step {α : Type*} (A : Set α) (F : α → α) (hH2 : Set.MapsTo F A A) (h : α → α) (hD1 : ∀ x : α, x ∈ A → h x = F x) :
    True := by
  -- 1. D1
  exact trivial

end Parley.Tests.Elaborator.ADefineCitedAsAStep.ADefineCitedAsAStep
