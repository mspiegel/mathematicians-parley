module

public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ramsey.TwoPointParts

theorem two_point_parts {α : Type*} (W : Set α) (v : α) (hH2 : ¬ v ∈ W) (Y : Set α) (hH3 : Y ⊆ W ∪ ({v} : Set α)) (hH4 : Y.encard = ((2 : ℕ) : ℕ∞)) :
    (Y ⊆ W ∨ (∃ w ∈ W, Y = ({v, w} : Set α))) := by
  -- 1. calculation
  have s1 : (W ∪ ({v} : Set α)) \ ({v} : Set α) = W := by
    calc (W ∪ ({v} : Set α)) \ ({v} : Set α) = W \ ({v} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := W) (a := v)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := W) (a := v))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := W) (a := v)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := W) (a := v)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := W) (a := v)); parley_set_side)
      _ = W := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := W) (a := v) hH2) | exact ((Parley.Items.Stdlib.Sets.mun_difference_absent (Y := W) (a := v) hH2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := W) (a := v) hH2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := W) (a := v) hH2) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := W) (a := v) hH2); parley_set_side)
  -- 2. mun:difference-shrinks, from H3
  have s2 : Y \ ({v} : Set α) ⊆ (W ∪ ({v} : Set α)) \ ({v} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := W ∪ ({v} : Set α)) (Y := Y) (Z := ({v} : Set α)) hH3) | exact ((Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := W ∪ ({v} : Set α)) (Y := Y) (Z := ({v} : Set α)) hH3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := W ∪ ({v} : Set α)) (Y := Y) (Z := ({v} : Set α)) hH3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := W ∪ ({v} : Set α)) (Y := Y) (Z := ({v} : Set α)) hH3) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := W ∪ ({v} : Set α)) (Y := Y) (Z := ({v} : Set α)) hH3); parley_set_side)
  -- 3. substitute (W ∪ {v}) ∖ {v} = W (line 1) into line 2
  have s3 : Y \ ({v} : Set α) ⊆ W := by parley_subst_at s1 s2
  -- 4. axi:excluded-middle P := v ∈ Y
  have s4 : v ∈ Y ∨ ¬ v ∈ Y := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := v ∈ Y)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := v ∈ Y))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := v ∈ Y)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := v ∈ Y)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := v ∈ Y)); parley_set_side)
  -- 5. cases, from 4
  have s5 : Y ⊆ W ∨ (∃ w ∈ W, Y = ({v, w} : Set α)) := by
    rcases s4 with hC1 | hC2
    · skip
      -- 5.1. calculation
      have s5_1 : (Y.ncard : ℤ) = 1 + 1 := by
        calc (Y.ncard : ℤ) = 2 := by parley_set_side
          _ = 1 + 1 := by norm_num
      -- 5.2. mun:card-remove X := Y, a := v, k := 1, from C1, 5.1
      have s5_2 : ((Y \ ({v} : Set α)).ncard : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := Y) (a := v) hC1 (k := 1) (by parley_set_side)); parley_set_side)
      -- 5.3. obtain w: mun:card-nonempty X := Y ∖ {v}, k := 0, from 5.2
      obtain ⟨w, s5_3, _⟩ := (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := Y \ ({v} : Set α)) (k := 0) (by parley_set_side))
      -- 5.4. mun:remove-member u := w, a := v, from 5.3
      have s5_4a : w ∈ Y := by first | exact (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).1; parley_set_side)
      have s5_4b : ¬ w = v := by first | exact (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := Y) (a := v) (u := w))).mp (by parley_set_side)).2; parley_set_side)
      -- 5.5. mun:in-subset, from 3, 5.3
      have s5_5 : w ∈ W := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := Y \ ({v} : Set α)) (Y := W) (u := w) s3 s5_3) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := Y \ ({v} : Set α)) (Y := W) (u := w) s3 s5_3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := Y \ ({v} : Set α)) (Y := W) (u := w) s3 s5_3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := Y \ ({v} : Set α)) (Y := W) (u := w) s3 s5_3) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := Y \ ({v} : Set α)) (Y := W) (u := w) s3 s5_3); parley_set_side)
      -- 5.6. mun:card-two a := v, b := w, from C1, H4, 5.4
      have s5_6 : Y = ({v, w} : Set α) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := v) (b := w) (by parley_set_side) hC1 s5_4a (by parley_set_side)) | exact ((Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := v) (b := w) (by parley_set_side) hC1 s5_4a (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := v) (b := w) (by parley_set_side) hC1 s5_4a (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := v) (b := w) (by parley_set_side) hC1 s5_4a (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := v) (b := w) (by parley_set_side) hC1 s5_4a (by parley_set_side)); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto) | (have h := (Parley.Items.Stdlib.Counting.mun_card_two (Y := Y) (a := v) (b := w) (by parley_set_side) hC1 s5_4a (by parley_set_side)); parley_set_side)
      -- 5.7. exhibit, from 5.5, 5.6
      have s5_7 : ∃ w ∈ W, Y = ({v, w} : Set α) := ⟨w, by parley_set_side, by parley_set_side⟩
      -- 5.8. mun:or-right, from 5.7
      have s5_8 : Y ⊆ W ∨ (∃ w ∈ W, Y = ({v, w} : Set α)) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_7) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_7)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_7) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_7) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_7); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_7); parley_set_side)
      all_goals parley_set_side
    · skip
      -- 5.9. mun:subset-into-difference, from C2, H3
      have s5_9 : Y ⊆ (W ∪ ({v} : Set α)) \ ({v} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := W ∪ ({v} : Set α)) (Y := Y) (a := v) hH3 hC2) | exact ((Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := W ∪ ({v} : Set α)) (Y := Y) (a := v) hH3 hC2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := W ∪ ({v} : Set α)) (Y := Y) (a := v) hH3 hC2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := W ∪ ({v} : Set α)) (Y := Y) (a := v) hH3 hC2) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := W ∪ ({v} : Set α)) (Y := Y) (a := v) hH3 hC2); parley_set_side)
      -- 5.10. substitute (W ∪ {v}) ∖ {v} = W (line 1) into line 5.9
      have s5_10 : Y ⊆ W := by parley_subst_at s1 s5_9
      -- 5.11. mun:or-left, from 5.10
      have s5_11 : Y ⊆ W ∨ (∃ w ∈ W, Y = ({v, w} : Set α)) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_10) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_10)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_10) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_10) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_10); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Y ⊆ W) (Q := ∃ w ∈ W, Y = ({v, w} : Set α)) s5_10); parley_set_side)
      all_goals parley_set_side
  all_goals exact s5

end Parley.Proofs.Wiedijk.Ramsey.TwoPointParts
