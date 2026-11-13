module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.ATripleInsideASubset

theorem a_triple_inside_a_subset {α : Type*} (X : Set α) (Y : Set α) (a : α) (hH3 : a ∈ X) (b : α) (hH4 : b ∈ X) (c : α) (hH5 : c ∈ X) (hH6 : X ⊆ Y) :
    ({c, a, b} : Set α) ⊆ Y := by
  -- 1. mun:triple-subset, from H3, H4, H5
  have s1 : ({a, b, c} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_triple_subset (X := X) (a := a) (b := b) (c := c) hH3 hH4 hH5)
  -- 2. mun:subset-transitive, from H6, 1
  exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({c, a, b} : Set α)) (Y := X) (Z := Y) (by (have h := s1; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.insert_subset_iff, Set.singleton_subset_iff] at h ⊢; all_goals tauto)) hH6)

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.ATripleInsideASubset
