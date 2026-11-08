module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.FiveSubstituted

theorem five_substituted {α : Type*} (X : Set α) (Y : Set α) (a : α) (b : α) (c : α) (d : α) (e : α) (hH8 : Y = ({a, b, c, d, e} : Set α)) (hH9 : Y ⊆ X) :
    ({e, c, a, d, b} : Set α) ⊆ X := by
  -- 1. substitute Y = {a, b, c, d, e} (H8) into H9
  parley_subst_at hH8 hH9

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.FiveSubstituted
