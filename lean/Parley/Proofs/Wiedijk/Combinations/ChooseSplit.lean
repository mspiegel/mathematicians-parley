module

public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/combinations.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Combinations.ChooseSplit

theorem choose_split {α : Type*} (X : Set α) (a : α) (hH2 : a ∈ X) (j : ℤ) (hH4 : X.Finite) :
    {S ∈ 𝒫 X | (S.ncard : ℤ) = j} = {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j} ∪ (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j - 1} := by
  set F : Set (Set α) := {S ∈ 𝒫 X | (S.ncard : ℤ) = j} with hD1
  have hD1_finite : F.Finite := by rw [hD1]; exact ((hH4).powerset).subset (fun _ h => h.1)
  set U : Set (Set α) := {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j} with hD2
  have hD2_finite : U.Finite := by rw [hD2]; exact (((hH4).subset (fun _ h => h.1)).powerset).subset (fun _ h => h.1)
  set V : Set (Set α) := {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j - 1} with hD3
  have hD3_finite : V.Finite := by rw [hD3]; exact (((hH4).subset (fun _ h => h.1)).powerset).subset (fun _ h => h.1)
  set W : Set (Set α) := (fun T : Set α => T ∪ ({a} : Set α)) '' V with hD4
  -- 1. proof
  have s1 : ∀ R ∈ F, R ∈ U ∪ W := by
    intro R hK1
    -- 1.1. def:part-builder u := R, from D1, K1
    have s1_1a : R ⊆ X := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).1
    have s1_1b : (R.ncard : ℤ) = j := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      have hI : (R.ncard : ℤ) = j := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).2)
      exact hI
    -- 1.2. axi:excluded-middle P := a ∈ R
    have s1_2 : a ∈ R ∨ ¬ a ∈ R := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a ∈ R))
    -- 1.3. cases, from 1.2
    rcases s1_2 with hC1 | hC2
    · skip
      -- 1.3.1. mun:member-nonempty, from C1
      have s1_3_1 : ¬ R = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_member_nonempty (Y := R) (a := a) hC1)
      -- 1.3.2. mun:card-at-least-one, from 1.3.1
      have s1_3_2 : (R.ncard : ℤ) ≥ 1 := by (have h := (Parley.Items.Stdlib.Counting.mun_card_at_least_one (X := R) s1_3_1); simp only [← Set.Finite.cast_ncard_eq (((hH4).subset s1_1a : (R : Set α).Finite))] at h ⊢; exact_mod_cast h)
      -- 1.3.3. substitute |R| = j (line 1.1) into line 1.3.2
      have s1_3_3 : j ≥ 1 := by parley_count_int; ((have h := Eq.subst (motive := (fun t : ℤ => t ≥ 1)) s1_1b s1_3_2; push_cast at h ⊢; all_goals exact_mod_cast h))
      -- 1.3.4. inequalities, from 1.3.3
      have s1_3_4 : 0 ≤ j - 1 := by parley_order
      -- 1.3.5. mun:nat0-as-int n := j − 1, from 1.3.4
      have s1_3_5 : 0 ≤ j - 1 := by
        have hI : 0 ≤ j - 1 := by parley_instance (((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := j - 1))).mpr ⟨by parley_set_side, s1_3_4⟩)
        exact hI
      -- 1.3.6. algebra, from 1.1
      have s1_3_6 : (R.ncard : ℤ) = j - 1 + 1 := by linear_combination (norm := parley_norm) s1_1b
      -- 1.3.7. mun:card-remove X := R, k := j − 1, from C1, 1.3.5, 1.3.6
      have s1_3_7 : ((R \ ({a} : Set α)).ncard : ℤ) = j - 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_remove (X := R) (a := a) hC1 (k := j - 1) s1_3_5 (by parley_set_side))
      -- 1.3.8. mun:difference-shrinks, from 1.1
      have s1_3_8 : R \ ({a} : Set α) ⊆ X \ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := X) (Y := R) (Z := ({a} : Set α)) s1_1a)
      -- 1.3.9. def:part-builder u := R ∖ {a}, X := X ∖ {a}, from D3, 1.3.7, 1.3.8
      have s1_3_9 : R \ ({a} : Set α) ∈ V := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j - 1)) (X := X \ ({a} : Set α)) (u := R \ ({a} : Set α)))).mpr ⟨s1_3_8, by parley_set_side⟩
      -- 1.3.10. mun:added-element-in-image Y := V, s := R ∖ {a}, from D4, 1.3.9
      have s1_3_10 : R \ ({a} : Set α) ∪ ({a} : Set α) ∈ W := by
        try simp only [hD4] at ⊢
        try push_cast at ⊢
        exact (Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := V) (s := R \ ({a} : Set α)) (a := a) s1_3_9)
      -- 1.3.11. substitute
      have s1_3_11 : R ∈ W := by
        have c1 : R \ ({a} : Set α) ∪ ({a} : Set α) = R := by exact (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := R) (a := a) hC1)
        have row1 : R ∈ W := by parley_subst_at c1 s1_3_10
        exact row1
      -- 1.3.12. mun:in-union-right, from 1.3.11
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := U) (Z := W) (u := R) s1_3_11)
    · skip
      -- 1.3.13. mun:subset-into-difference, from C2, 1.1
      have s1_3_13 : R ⊆ X \ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := X) (Y := R) (a := a) s1_1a hC2)
      -- 1.3.14. def:part-builder u := R, X := X ∖ {a}, from D2, 1.1, 1.3.13
      have s1_3_14 : R ∈ U := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X \ ({a} : Set α)) (u := R))).mpr ⟨s1_3_13, by parley_set_side⟩
      -- 1.3.15. mun:in-union-left, from 1.3.14
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := U) (Z := W) (u := R) s1_3_14)
  -- 2. def:subset, from 1
  have s2 : F ⊆ U ∪ W := ((Parley.Items.Stdlib.Sets.def_subset (X := F) (Y := U ∪ W))).mpr s1
  -- 3. mun:difference-subset
  have s3 : X \ ({a} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({a} : Set α)))
  -- 4. proof
  have s4 : ∀ R ∈ U, R ∈ F := by
    intro R hK2
    -- 4.1. def:part-builder u := R, X := X ∖ {a}, from D2, K2
    have s4_1a : R ⊆ X \ ({a} : Set α) := by
      try simp only [hD2] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X \ ({a} : Set α)) (u := R))).mp (by parley_set_side)).1
    have s4_1b : (R.ncard : ℤ) = j := by
      try simp only [hD2] at ⊢
      try push_cast at ⊢
      have hI : (R.ncard : ℤ) = j := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X \ ({a} : Set α)) (u := R))).mp (by parley_set_side)).2)
      exact hI
    -- 4.2. mun:subset-transitive, from 3, 4.1
    have s4_2 : R ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := R) (Y := X \ ({a} : Set α)) (Z := X) s4_1a s3)
    -- 4.3. def:part-builder u := R, from D1, 4.1, 4.2
    exact ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mpr ⟨s4_2, by parley_set_side⟩
  -- 5. def:subset, from 4
  have s5 : U ⊆ F := ((Parley.Items.Stdlib.Sets.def_subset (X := U) (Y := F))).mpr s4
  -- 6. proof
  have s6 : ∀ T ∈ V, T ∪ ({a} : Set α) ∈ F := by
    intro T hK3
    -- 6.1. def:part-builder u := T, X := X ∖ {a}, from D3, K3
    have s6_1a : T ⊆ X \ ({a} : Set α) := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j - 1)) (X := X \ ({a} : Set α)) (u := T))).mp (by parley_set_side)).1
    have s6_1b : (T.ncard : ℤ) = j - 1 := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      have hI : (T.ncard : ℤ) = j - 1 := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j - 1)) (X := X \ ({a} : Set α)) (u := T))).mp (by parley_set_side)).2)
      exact hI
    -- 6.2. mun:subset-transitive, from 3, 6.1
    have s6_2 : T ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := T) (Y := X \ ({a} : Set α)) (Z := X) s6_1a s3)
    -- 6.3. mun:singleton-subset, from H2
    have s6_3 : ({a} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := a) hH2)
    -- 6.4. mun:union-subset, from 6.2, 6.3
    have s6_4 : T ∪ ({a} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := T) (Y := ({a} : Set α)) (Z := X) s6_2 s6_3)
    -- 6.5. mun:finite-part, from H4, 6.2
    have s6_5 : T.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := T) hH4 s6_2)
    -- 6.6. mun:subset-of-difference, from 6.1
    have s6_6 : ¬ a ∈ T := by exact (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := X) (Y := T) (a := a) s6_1a)
    -- 6.7. mun:card-add-one, from 6.5, 6.6
    have s6_7 : ((T ∪ ({a} : Set α)).ncard : ℤ) = (T.ncard : ℤ) + 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_add_one (X := T) (a := a) s6_5 s6_6)
    -- 6.8. algebra, from 6.1, 6.7
    have s6_8 : ((T ∪ ({a} : Set α)).ncard : ℤ) = j := by parley_count_int; (linear_combination (norm := parley_norm) s6_1b + s6_7)
    -- 6.9. def:part-builder u := T ∪ {a}, from D1, 6.4, 6.8
    exact ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := T ∪ ({a} : Set α)))).mpr ⟨s6_4, by parley_set_side⟩
  -- 7. mun:added-elements-stay-inside Y := V, Z := F, from D4, 6
  have s7 : W ⊆ F := by
    try simp only [hD4] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := V) (Z := F) (a := a) s6)
  -- 8. mun:union-subset, from 5, 7
  have s8 : U ∪ W ⊆ F := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := U) (Y := W) (Z := F) s5 s7)
  -- 9. mun:subset-antisymmetric, from D1, D2, D3, D4, 2, 8
  try simp only [hD1, hD2, hD3, hD4] at ⊢
  try push_cast at ⊢
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := {S ∈ 𝒫 X | (S.ncard : ℤ) = j}) (Y := {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j} ∪ (fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j - 1}) (by parley_set_side) (by parley_set_side))

end Parley.Proofs.Wiedijk.Combinations.ChooseSplit
