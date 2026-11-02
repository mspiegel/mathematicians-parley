module

public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairCitedInTheOtherOrder

theorem a_pair_cited_in_the_other_order {α : Type*} (Y : Set α) (hH2 : Y.encard = ((2 : ℕ) : ℕ∞)) (v : α) (hH3 : v ∈ Y) (w : α) (hH4 : w ∈ Y) (hH5 : ¬ v = w) :
    Y = ({v, w} : Set α) := by
  -- 1. mun:card-two a := w, b := v, from H2, H3, H4, H5
  have s1 : Y = ({v, w} : Set α) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_side) (by parley_side) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_side) (by parley_side) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_side) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_side) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_side) (by parley_side) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_side) (by parley_side) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairCitedInTheOtherOrder
