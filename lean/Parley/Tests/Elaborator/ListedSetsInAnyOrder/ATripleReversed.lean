module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.ATripleReversed

theorem a_triple_reversed {α : Type*} (X : Set α) (Y : Set α) (a : α) (hH3 : a ∈ X) (b : α) (hH4 : b ∈ X) (c : α) (hH5 : c ∈ X) (hH6 : X ⊆ Y) :
    ({c, b, a} : Set α) ⊆ Y := by
  -- 1. mun:triple-subset, from H3, H4, H5
  have s1 : ({a, b, c} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_triple_subset (X := X) (a := a) (b := b) (c := c) hH3 hH4 hH5) | exact ((Parley.Items.Stdlib.Sets.mun_triple_subset (X := X) (a := a) (b := b) (c := c) hH3 hH4 hH5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_triple_subset (X := X) (a := a) (b := b) (c := c) hH3 hH4 hH5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_triple_subset (X := X) (a := a) (b := b) (c := c) hH3 hH4 hH5) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_subset (X := X) (a := a) (b := b) (c := c) hH3 hH4 hH5); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_subset (X := X) (a := a) (b := b) (c := c) hH3 hH4 hH5); parley_set_side)
  -- 2. mun:subset-transitive, from H6, 1
  have s2 : ({c, b, a} : Set α) ⊆ Y := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({c, b, a} : Set α)) (Y := X) (Z := Y) (by parley_set_side) hH6) | exact ((Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({c, b, a} : Set α)) (Y := X) (Z := Y) (by parley_set_side) hH6)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({c, b, a} : Set α)) (Y := X) (Z := Y) (by parley_set_side) hH6) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({c, b, a} : Set α)) (Y := X) (Z := Y) (by parley_set_side) hH6) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({c, b, a} : Set α)) (Y := X) (Z := Y) (by parley_set_side) hH6); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({c, b, a} : Set α)) (Y := X) (Z := Y) (by parley_set_side) hH6); parley_set_side)
  all_goals exact s2

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.ATripleReversed
