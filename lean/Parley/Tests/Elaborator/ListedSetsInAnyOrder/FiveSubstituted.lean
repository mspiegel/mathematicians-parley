module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.FiveSubstituted

theorem five_substituted {α : Type*} (X : Set α) (Y : Set α) (a : α) (b : α) (c : α) (d : α) (e : α) (hH8 : Y = ({a, b, c, d, e} : Set α)) (hH9 : Y ⊆ X) :
    ({e, c, a, d, b} : Set α) ⊆ X := by
  -- 1. substitute Y = {a, b, c, d, e} (H8) into H9
  have s1 : ({e, c, a, d, b} : Set α) ⊆ X := by parley_subst_at hH8 hH9
  all_goals exact s1

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.FiveSubstituted
