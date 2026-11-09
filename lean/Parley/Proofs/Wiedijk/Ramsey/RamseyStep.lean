module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ramsey.GrowByOne

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ramsey.RamseyStep

set_option maxHeartbeats 1200000 in
theorem ramsey_step {α : Type*} (V : Set α) (E : Set (Set α)) (F : Set (Set α)) (k : ℤ) (hH1 : 0 < k) (j : ℤ) (hH2 : 0 < j) (hH4 : V.Finite) (hH7 : ∀ Y ∈ 𝒫 V, (Y.ncard : ℤ) = 2 → Y ∈ E ∨ Y ∈ F) (X : Set α) (hH8 : X ⊆ V) (hH9 : (LeanBridges.Counting.choose (k + j) k : ℤ) ≤ (X.ncard : ℤ)) (hH10 : ∀ Z ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (Z.ncard : ℤ) → (∃ W ∈ 𝒫 Z, k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F))) (hH11 : ∀ Z ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) k : ℤ) ≤ (Z.ncard : ℤ) → (∃ W ∈ 𝒫 Z, k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F))) :
    (∃ W ∈ 𝒫 X, k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by
  -- 1. mun:finite-part, from H4, H8
  have s1 : X.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hH8)
  -- 2. inequalities, from H2
  have s2 : k ≤ k + j := by parley_order
  -- 3. def:range0 n := k + j, from 2
  have s3 : k ∈ Finset.Icc (0 : ℤ) (k + j) := ((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := k + j) (by parley_set_side))).mpr (by parley_set_side)
  -- 4. mun:binomial-nat, from 3
  have s4 : 0 < (LeanBridges.Counting.choose (k + j) k : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat (n := k + j) (by parley_set_side) (k := k) s3)
  -- 5. inequalities, from 4
  have s5 : 1 ≤ (LeanBridges.Counting.choose (k + j) k : ℤ) := by parley_order
  -- 6. transitivity, from 5, H9
  have r319_1 : 0 ≤ (X.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) s1)
  have s6 : 1 ≤ (X.ncard : ℤ) := by parley_count_int; (parley_order)
  -- 7. inequalities, from 6
  have r323_1 : 0 ≤ (X.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) s1)
  have s7 : 0 < (X.ncard : ℤ) := by parley_count_int; (parley_order)
  -- 8. mun:card-positive, from 7
  have s8 : ¬ X = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_positive (X := X) (by parley_set_side))
  -- 9. obtain v: mun:nonempty-member, from 8
  obtain ⟨v, s9, _⟩ := (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := X) s8)
  set R : Set α := {w ∈ X \ ({v} : Set α) | ({v, w} : Set α) ∈ E} with hD2
  set B : Set α := {w ∈ X \ ({v} : Set α) | ¬ ({v, w} : Set α) ∈ E} with hD3
  -- 10. mun:set-builder-split, from D2, D3
  have s10 : X \ ({v} : Set α) = R ∪ B := by
    try simp only [hD2, hD3] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_split (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)))
  -- 11. mun:set-builder-split-disjoint, from D2, D3
  have s11 : R ∩ B = ∅ := by
    try simp only [hD2, hD3] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_split_disjoint (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)))
  -- 12. mun:difference-subset
  have s12 : X \ ({v} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({v} : Set α)))
  -- 13. mun:finite-part, from 1, 12
  have s13 : (X \ ({v} : Set α)).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := X \ ({v} : Set α)) s1 s12)
  -- 14. mun:set-builder-subset, from D2
  have s14 : R ⊆ X \ ({v} : Set α) := by
    try simp only [hD2] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)))
  -- 15. mun:set-builder-subset, from D3
  have s15 : B ⊆ X \ ({v} : Set α) := by
    try simp only [hD3] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun w : α => ¬ ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)))
  -- 16. mun:finite-part, from 13, 14
  have s16 : R.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X \ ({v} : Set α)) (Y := R) s13 s14)
  -- 17. mun:finite-part, from 13, 15
  have s17 : B.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X \ ({v} : Set α)) (Y := B) s13 s15)
  -- 18. mun:card-nat0, from 16
  have s18 : 0 ≤ (R.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := R) s16)
  -- 19. mun:card-nat0, from 17
  have s19 : 0 ≤ (B.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) s17)
  -- 20. mun:card-disjoint-union X := R, Y := B, m := |R|, n := |B|, from 11, 18, 19
  have s20 : ((R ∪ B).ncard : ℤ) = (R.ncard : ℤ) + (B.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := R) (Y := B) (m := (R.ncard : ℤ)) (by parley_set_side) (n := (B.ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s11)
  -- 21. substitute X ∖ {v} = R ∪ B (line 10) into line 20
  have s21 : ((X \ ({v} : Set α)).ncard : ℤ) = (R.ncard : ℤ) + (B.ncard : ℤ) := by parley_subst_at s10 s20
  -- 22. mun:card-add-one, from 13
  have r375_1 : ¬ v ∈ X \ ({v} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_not_in_difference (X := X) (a := v))
  have s22 : ((X \ ({v} : Set α) ∪ ({v} : Set α)).ncard : ℤ) = ((X \ ({v} : Set α)).ncard : ℤ) + 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_add_one (X := X \ ({v} : Set α)) (a := v) s13 r375_1)
  -- 23. substitute
  have s23 : (X.ncard : ℤ) = (R.ncard : ℤ) + (B.ncard : ℤ) + 1 := by parley_count_after (by
    have c1 : X \ ({v} : Set α) ∪ ({v} : Set α) = X := by exact (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := X) (a := v) s9)
    have row1 : (X.ncard : ℤ) = ((X \ ({v} : Set α)).ncard : ℤ) + 1 := by parley_subst_at c1 s22
    have c2 : ((X \ ({v} : Set α)).ncard : ℤ) = (R.ncard : ℤ) + (B.ncard : ℤ) := by parley_subst s21
    have row2 : (X.ncard : ℤ) = (R.ncard : ℤ) + (B.ncard : ℤ) + 1 := by parley_subst_at c2 row1
    exact row2)
  -- 24. mun:nat-minus-one n := k + j
  have s24 : 0 ≤ k + j - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := k + j) (by parley_set_side))
  -- 25. mun:binomial-nat0, from 24
  have s25 : 0 ≤ (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := k + j - 1) (by parley_set_side) (k := k - 1))
  -- 26. mun:binomial-nat0, from 24
  have s26 : 0 ≤ (LeanBridges.Counting.choose (k + j - 1) k : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := k + j - 1) (by parley_set_side) (k := k))
  -- 27. algebra
  have s27 : k + j - 1 + 1 = k + j := by parley_ring
  -- 28. calculation
  have s28 : (LeanBridges.Counting.choose (k + j - 1) k : ℤ) + (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (R.ncard : ℤ) + (B.ncard : ℤ) + 1 := by parley_count_after (by
    calc (LeanBridges.Counting.choose (k + j - 1) k : ℤ) + (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) = (LeanBridges.Counting.choose (k + j - 1 + 1) k : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := k + j - 1) (by parley_set_side) (k := k))
      _ = (LeanBridges.Counting.choose (k + j) k : ℤ) := by parley_subst s27
      _ ≤ (X.ncard : ℤ) := by parley_set_side
      _ = (R.ncard : ℤ) + (B.ncard : ℤ) + 1 := by parley_set_side)
  -- 29. axi:excluded-middle P := C(k + j − 1, k − 1) ≤ |R|
  have s29 : (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (R.ncard : ℤ) ∨ ¬ (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (R.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (R.ncard : ℤ)))
  -- 30. cases, from 29
  have s30 : (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (R.ncard : ℤ) ∨ (LeanBridges.Counting.choose (k + j - 1) k : ℤ) ≤ (B.ncard : ℤ) := by
    rcases s29 with hC1 | hC2
    · skip
      -- 30.1. mun:or-left, from C1
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (R.ncard : ℤ)) (Q := (LeanBridges.Counting.choose (k + j - 1) k : ℤ) ≤ (B.ncard : ℤ)) (by parley_set_side))
    · skip
      -- 30.2. inequalities, from C2, 18, 25
      have s30_2 : (R.ncard : ℤ) < (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) := by parley_order
      -- 30.3. mun:integer-step, from 18, 25, 30.2
      have s30_3 : (R.ncard : ℤ) + 1 ≤ (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (R.ncard : ℤ)) (n := (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ)) (by parley_set_side))
      -- 30.4. inequalities
      have r426_1 : 0 ≤ (R.ncard : ℤ) := by parley_set_side
      have r426_2 : 0 ≤ (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) := by parley_set_side
      have r426_3 : 0 ≤ (LeanBridges.Counting.choose (k + j - 1) k : ℤ) := by parley_set_side
      have s30_4 : (LeanBridges.Counting.choose (k + j - 1) k : ℤ) + ((R.ncard : ℤ) + 1) ≤ (LeanBridges.Counting.choose (k + j - 1) k : ℤ) + (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) := by parley_order
      -- 30.5. transitivity, from 30.4, 28
      have r434_1 : 0 ≤ (R.ncard : ℤ) := by parley_set_side
      have r434_2 : 0 ≤ (B.ncard : ℤ) := by parley_set_side
      have r434_3 : 0 ≤ (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) := by parley_set_side
      have r434_4 : 0 ≤ (LeanBridges.Counting.choose (k + j - 1) k : ℤ) := by parley_set_side
      have s30_5 : (LeanBridges.Counting.choose (k + j - 1) k : ℤ) + ((R.ncard : ℤ) + 1) ≤ (R.ncard : ℤ) + (B.ncard : ℤ) + 1 := by parley_order
      -- 30.6. inequalities
      have r441_1 : 0 ≤ (R.ncard : ℤ) := by parley_set_side
      have r441_2 : 0 ≤ (B.ncard : ℤ) := by parley_set_side
      have r441_3 : 0 ≤ (LeanBridges.Counting.choose (k + j - 1) k : ℤ) := by parley_set_side
      have s30_6 : (LeanBridges.Counting.choose (k + j - 1) k : ℤ) ≤ (B.ncard : ℤ) := by parley_order
      -- 30.7. mun:or-right, from 30.6
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (R.ncard : ℤ)) (Q := (LeanBridges.Counting.choose (k + j - 1) k : ℤ) ≤ (B.ncard : ℤ)) (by parley_set_side))
  -- 31. mun:subset-transitive, from H8, 12
  have s31 : X \ ({v} : Set α) ⊆ V := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := X \ ({v} : Set α)) (Y := X) (Z := V) s12 hH8)
  -- 32. cases, from 30
  rcases s30 with hC3 | hC4
  · skip
    -- 32.1. mun:subset-transitive, from 14, 31
    have s32_1 : R ⊆ V := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := R) (Y := X \ ({v} : Set α)) (Z := V) s14 s31)
    -- 32.2. instantiate Z := R in H10, from C3, 32.1
    have s32_2 : ∃ W ∈ 𝒫 R, k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F) := by exact (hH10 R (by parley_set_side) (by parley_set_side))
    -- 32.3. obtain W from line 32.2
    obtain ⟨W, s32_3a, s32_3b⟩ := s32_2
    -- 32.4. def:set-builder, from D2
    have s32_4 : ∀ w ∈ R, ({v, w} : Set α) ∈ E := by
      intro w h_w
      try simp only [hD2] at *
      try push_cast at *
      first | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp (by parley_set_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp (by parley_set_side); parley_set_side)
    -- 32.5. thm:grow-by-one N := R, j := j + 1, from 1, 9, 14, 32.3, 32.4
    first | exact (Parley.Proofs.Wiedijk.Ramsey.GrowByOne.grow_by_one (X := X) (E := E) (F := F) s1 (k := k) (by parley_set_side) (j := j + 1) (by parley_set_side) (v := v) s9 (N := R) (by parley_set_side) s32_4 (W := W) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Proofs.Wiedijk.Ramsey.GrowByOne.grow_by_one (X := X) (E := E) (F := F) s1 (k := k) (by parley_set_side) (j := j + 1) (by parley_set_side) (v := v) s9 (N := R) (by parley_set_side) s32_4 (W := W) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Proofs.Wiedijk.Ramsey.GrowByOne.grow_by_one (X := X) (E := E) (F := F) s1 (k := k) (by parley_set_side) (j := j + 1) (by parley_set_side) (v := v) s9 (N := R) (by parley_set_side) s32_4 (W := W) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Ramsey.GrowByOne.grow_by_one (X := X) (E := E) (F := F) s1 (k := k) (by parley_set_side) (j := j + 1) (by parley_set_side) (v := v) s9 (N := R) (by parley_set_side) s32_4 (W := W) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Proofs.Wiedijk.Ramsey.GrowByOne.grow_by_one (X := X) (E := E) (F := F) s1 (k := k) (by parley_set_side) (j := j + 1) (by parley_set_side) (v := v) s9 (N := R) (by parley_set_side) s32_4 (W := W) (by parley_set_side) (by parley_set_side)); parley_set_side)
  · skip
    -- 32.6. mun:subset-transitive, from 15, 31
    have s32_6 : B ⊆ V := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := B) (Y := X \ ({v} : Set α)) (Z := V) s15 s31)
    -- 32.7. instantiate Z := B in H11, from C4, 32.6
    have s32_7 : ∃ W ∈ 𝒫 B, k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F) := by exact (hH11 B (by parley_set_side) (by parley_set_side))
    -- 32.8. obtain W from line 32.7
    obtain ⟨W, s32_8a, s32_8b⟩ := s32_7
    -- 32.9. mun:or-swap, from 32.8
    have s32_9 : j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F) ∨ k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_swap (P := k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) (by parley_set_side))
    -- 32.10. proof
    have s32_10 : ∀ w ∈ B, ({v, w} : Set α) ∈ F := by
      intro w hK1
      -- 32.10.1. def:set-builder u := w, from D3, K1
      have s32_10_1a : w ∈ X \ ({v} : Set α) := by
        try simp only [hD3] at *
        try push_cast at *
        exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ¬ ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp hK1).1
      have s32_10_1b : ¬ ({v, w} : Set α) ∈ E := by
        try simp only [hD3] at *
        try push_cast at *
        exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun w : α => ¬ ({v, w} : Set α) ∈ E)) (X := X \ ({v} : Set α)) (u := w))).mp hK1).2
      -- 32.10.2. mun:remove-member u := w, Y := X, a := v, from 32.10.1
      have s32_10_2a : w ∈ X := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := X) (a := v) (u := w))).mp s32_10_1a).1
      have s32_10_2b : ¬ w = v := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := X) (a := v) (u := w))).mp s32_10_1a).2
      -- 32.10.3. mun:pair-subset a := v, b := w, from 9, 32.10.2
      have s32_10_3 : ({v, w} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := v) (b := w) s9 s32_10_2a)
      -- 32.10.4. mun:subset-transitive, from H8, 32.10.3
      have s32_10_4 : ({v, w} : Set α) ⊆ V := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := ({v, w} : Set α)) (Y := X) (Z := V) s32_10_3 hH8)
      -- 32.10.5. mun:card-pair-distinct u := v, from 32.10.2
      have s32_10_5 : (({v, w} : Set α).ncard : ℤ) = 2 := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b) | exact_mod_cast (((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b)).symm | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := v) (w := w))).mp (Ne.symm s32_10_2b); parley_set_side)
      -- 32.10.6. instantiate Y := {v, w} in H7, from 32.10.4, 32.10.5
      have s32_10_6 : ({v, w} : Set α) ∈ E ∨ ({v, w} : Set α) ∈ F := by exact (hH7 ({v, w} : Set α) (by parley_set_side) (by parley_set_side))
      -- 32.10.7. mun:disjunctive-syllogism-left, from 32.10.1, 32.10.6
      exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ({v, w} : Set α) ∈ E) (Q := ({v, w} : Set α) ∈ F) s32_10_6 s32_10_1b)
    -- 32.11. obtain U: thm:grow-by-one N := B, E := F, F := E, k := j, j := k + 1, from 1, 9, 15, 32.8, 32.9, 32.10
    obtain ⟨U, s32_11a, s32_11b⟩ := (Parley.Proofs.Wiedijk.Ramsey.GrowByOne.grow_by_one (X := X) (E := F) (F := E) s1 (k := j) (by parley_set_side) (j := k + 1) (by parley_set_side) (v := v) s9 (N := B) (by parley_set_side) s32_10 (W := W) (by parley_set_side) (by parley_set_side))
    -- 32.12. mun:or-swap, from 32.11
    have s32_12 : k + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ F) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_swap (P := j + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ F)) (Q := k + 1 ≤ (U.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 U, (Y.ncard : ℤ) = 2 → Y ∈ E)) (by parley_set_side))
    -- 32.13. exhibit, from 32.11, 32.12
    exact ⟨U, by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Ramsey.RamseyStep
