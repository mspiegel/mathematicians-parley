module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairInsideASubset

theorem a_pair_inside_a_subset {α : Type*} (X : Set α) (u : α) (hH2 : u ∈ X) (w : α) (hH3 : w ∈ X) :
    ({w, u} : Set α) ⊆ X := by
  -- 1. mun:pair-subset a := u, b := w, from H2, H3
  (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) hH2 hH3); simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.insert_subset_iff, Set.singleton_subset_iff] at h ⊢; all_goals tauto)

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairInsideASubset
