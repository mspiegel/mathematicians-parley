module

public import NormTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Proofs.Wiedijk.Ramsey
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Ramsey.TwoPointParts

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ramsey.GrowByOne

set_option maxHeartbeats 600000 in
theorem grow_by_one {α : Type*} (X : Set α) (E : Set (Set α)) (F : Set (Set α)) (hH2 : X.Finite) (k : ℤ) (hH5 : 0 < k) (j : ℤ) (hH6 : 0 < j) (v : α) (hH7 : v ∈ X) (N : Set α) (hH8 : N ⊆ X \ ({v} : Set α)) (hH9 : ∀ w ∈ N, ({v, w} : Set α) ∈ E) (W : Set α) (hH10 : W ⊆ N) (hH11 : k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) :
    (∃ U ∈ 𝒫 X, k + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by
  -- 1. mun:difference-subset
  have s1 : X \ ({v} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({v} : Set α))) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({v} : Set α)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({v} : Set α))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({v} : Set α))) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({v} : Set α))); parley_set_side)
  -- 2. mun:subset-transitive, from H8, H10
  have s2 : W ⊆ X \ ({v} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := N) (Z := X \ ({v} : Set α)) hH10 hH8) | exact ((Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := N) (Z := X \ ({v} : Set α)) hH10 hH8)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := N) (Z := X \ ({v} : Set α)) hH10 hH8) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := N) (Z := X \ ({v} : Set α)) hH10 hH8) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := N) (Z := X \ ({v} : Set α)) hH10 hH8); parley_set_side)
  -- 3. mun:subset-transitive, from 1, 2
  have s3 : W ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := X \ ({v} : Set α)) (Z := X) s2 s1) | exact ((Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := X \ ({v} : Set α)) (Z := X) s2 s1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := X \ ({v} : Set α)) (Z := X) s2 s1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := X \ ({v} : Set α)) (Z := X) s2 s1) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := W) (Y := X \ ({v} : Set α)) (Z := X) s2 s1); parley_set_side)
  -- 4. cases, from H11
  have s4 : ∃ U ∈ 𝒫 X, k + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ F) := by
    rcases hH11 with hC1 | hC4
    · skip
      -- 4.1. D1, from C1
      have s4_1 : k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) := by parley_set_side
      -- 4.2. mun:subset-of-difference, from 2
      have s4_2 : ¬ v ∈ W := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := X) (Y := W) (a := v) s2) | exact ((Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := X) (Y := W) (a := v) s2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := X) (Y := W) (a := v) s2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := X) (Y := W) (a := v) s2) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := X) (Y := W) (a := v) s2); parley_set_side)
      -- 4.3. mun:finite-part, from H2, 3
      have s4_3 : W.Finite := by first | exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := W) hH2 s3) | exact ((Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := W) hH2 s3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := W) hH2 s3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := W) hH2 s3) | (have h := (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := W) hH2 s3); parley_set_side)
      -- 4.4. inequalities
      have r215_1 : 0 ≤ (W.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := W) s4_3) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := W) s4_3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := W) s4_3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := W) s4_3) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := W) s4_3); parley_set_side)
      have s4_4 : k + 1 ≤ (W.ncard : ℤ) + 1 := by parley_count_int; (parley_order)
      -- 4.5. calculation
      have s4_5 : k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) := by parley_count_after (by
        calc k + 1 ≤ (W.ncard : ℤ) + 1 := by parley_set_side
          _ = ((W ∪ ({v} : Set α)).ncard : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := W) (a := v) s4_3 s4_2); parley_set_side))
      -- 4.6. proof
      have s4_6 : ∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E := by
        intro Y hK1
        intro hK2
        -- 4.6.1. thm:two-point-parts, from K1, K2, 4.2
        have s4_6_1 : Y ⊆ W ∨ (∃ w ∈ W, Y = ({v, w} : Set α)) := by first | exact (Parley.Proofs.Wiedijk.Ramsey.TwoPointParts.two_point_parts (W := W) (v := v) s4_2 (Y := Y) hK1 (by parley_set_side)) | exact ((Parley.Proofs.Wiedijk.Ramsey.TwoPointParts.two_point_parts (W := W) (v := v) s4_2 (Y := Y) hK1 (by parley_set_side))).symm | simpa using (Parley.Proofs.Wiedijk.Ramsey.TwoPointParts.two_point_parts (W := W) (v := v) s4_2 (Y := Y) hK1 (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Ramsey.TwoPointParts.two_point_parts (W := W) (v := v) s4_2 (Y := Y) hK1 (by parley_set_side)) | (have h := (Parley.Proofs.Wiedijk.Ramsey.TwoPointParts.two_point_parts (W := W) (v := v) s4_2 (Y := Y) hK1 (by parley_set_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.Ramsey.TwoPointParts.two_point_parts (W := W) (v := v) s4_2 (Y := Y) hK1 (by parley_set_side)); parley_set_side)
        -- 4.6.2. cases, from 4.6.1
        have s4_6_2 : Y ∈ E := by
          rcases s4_6_1 with hC2 | hC3
          · skip
            -- 4.6.2.1. instantiate Y := Y in line 4.1, from C2, K2
            have s4_6_2_1 : Y ∈ E := by first | exact (s4_1.2 Y (by parley_set_side) (by parley_set_side)) | exact ((s4_1.2 Y (by parley_set_side) (by parley_set_side))).symm | simpa using (s4_1.2 Y (by parley_set_side) (by parley_set_side)) | exact_mod_cast (s4_1.2 Y (by parley_set_side) (by parley_set_side)) | (have h := (s4_1.2 Y (by parley_set_side) (by parley_set_side)); parley_set_side)
            all_goals parley_set_side
          · skip
            -- 4.6.2.2. obtain w from C3
            obtain ⟨w, s4_6_2_2a, s4_6_2_2b⟩ := hC3
            -- 4.6.2.3. mun:in-subset, from H10, 4.6.2.2
            have s4_6_2_3 : w ∈ N := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := N) (u := w) hH10 s4_6_2_2a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := N) (u := w) hH10 s4_6_2_2a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := N) (u := w) hH10 s4_6_2_2a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := N) (u := w) hH10 s4_6_2_2a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := N) (u := w) hH10 s4_6_2_2a); parley_set_side)
            -- 4.6.2.4. instantiate w := w in H9, from 4.6.2.3
            have s4_6_2_4 : ({v, w} : Set α) ∈ E := by first | exact (hH9 w (by parley_set_side)) | exact ((hH9 w (by parley_set_side))).symm | simpa using (hH9 w (by parley_set_side)) | exact_mod_cast (hH9 w (by parley_set_side)) | (have h := (hH9 w (by parley_set_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (hH9 w (by parley_set_side)); parley_set_side)
            -- 4.6.2.5. substitute Y = {v, w} (line 4.6.2.2) into line 4.6.2.4
            have s4_6_2_5 : Y ∈ E := by parley_subst_at s4_6_2_2b s4_6_2_4
            all_goals parley_set_side
        all_goals parley_set_side
      -- 4.7. mun:singleton-subset, from H7
      have s4_7 : ({v} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) hH7) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) hH7)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) hH7) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) hH7) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) hH7); parley_set_side)
      -- 4.8. mun:union-subset, from 3, 4.7
      have s4_8 : W ∪ ({v} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := ({v} : Set α)) (Z := X) s3 s4_7) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := ({v} : Set α)) (Z := X) s3 s4_7)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := ({v} : Set α)) (Z := X) s3 s4_7) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := ({v} : Set α)) (Z := X) s3 s4_7) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := ({v} : Set α)) (Z := X) s3 s4_7); parley_set_side)
      -- 4.9. D1, from 4.5, 4.6
      have s4_9 : k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E) := by parley_set_side
      -- 4.10. mun:or-left, from 4.9
      have s4_10 : k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ F) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := k + 1 ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ ((W ∪ ({v} : Set α)).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 (W ∪ ({v} : Set α)), (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)); parley_set_side)
      -- 4.11. exhibit, from 4.8, 4.10
      have s4_11 : ∃ U ∈ 𝒫 X, k + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ F) := ⟨W ∪ ({v} : Set α), by parley_set_side, by parley_set_side⟩
      all_goals parley_set_side
    · skip
      -- 4.12. mun:or-right, from C4
      have s4_12 : k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side)); parley_set_side)
      -- 4.13. exhibit, from 3, 4.12
      have s4_13 : ∃ U ∈ 𝒫 X, k + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ F) := ⟨W, by parley_set_side, by parley_set_side⟩
      all_goals parley_set_side
  all_goals exact s4

end Parley.Proofs.Wiedijk.Ramsey.GrowByOne
