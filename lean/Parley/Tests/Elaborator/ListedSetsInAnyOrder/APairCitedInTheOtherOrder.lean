module

public import SetTactics
public import Tactics
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairCitedInTheOtherOrder

theorem a_pair_cited_in_the_other_order {α : Type*} (Y : Set α) (hH2 : Y.encard = ((2 : ℕ) : ℕ∞)) (v : α) (hH3 : v ∈ Y) (w : α) (hH4 : w ∈ Y) (hH5 : ¬ v = w) :
    Y = ({v, w} : Set α) := by
  -- 1. mun:card-two a := w, b := v, from H2, H3, H4, H5
  first | exact (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_set_side) hH4 hH3 (Ne.symm hH5)) | exact ((Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_set_side) hH4 hH3 (Ne.symm hH5))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_set_side) hH4 hH3 (Ne.symm hH5)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_set_side) hH4 hH3 (Ne.symm hH5)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_set_side) hH4 hH3 (Ne.symm hH5)); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := w) (b := v) (by parley_set_side) hH4 hH3 (Ne.symm hH5)); parley_set_side)

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairCitedInTheOtherOrder
