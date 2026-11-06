module

public import SetTactics
public import Tactics
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairCitedInTheOtherOrder

theorem a_pair_cited_in_the_other_order {α : Type*} (Y : Set α) (hH2 : Y.encard = ((2 : ℕ) : ℕ∞)) (v : α) (hH3 : v ∈ Y) (w : α) (hH4 : w ∈ Y) (hH5 : ¬ v = w) :
    Y = ({v, w} : Set α) := by
  -- 1. mun:card-two a := w, b := v, from H2, H3, H4, H5
  have s1 : Y = ({v, w} : Set α) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) hH2 hH4 hH3 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) hH2 hH4 hH3 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) hH2 hH4 hH3 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) hH2 hH4 hH3 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) hH2 hH4 hH3 (by parley_set_side)); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) hH2 hH4 hH3 (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairCitedInTheOtherOrder
