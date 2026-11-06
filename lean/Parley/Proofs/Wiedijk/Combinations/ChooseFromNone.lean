module

public import ArithTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/combinations.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Combinations.ChooseFromNone

set_option maxHeartbeats 600000 in
theorem choose_from_none {α : Type*} (X : Set α) (j : ℤ) (hH3 : X.encard = ((0 : ℕ) : ℕ∞)) :
    ({S ∈ 𝒫 X | (S.ncard : ℤ) = j}.ncard : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by
  set F : Set (Set α) := {S ∈ 𝒫 X | (S.ncard : ℤ) = j} with hD1
  -- 1. mun:card-zero, from H3
  have s1 : X = ∅ := by first | exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := X) hH3) | exact ((Parley.Items.Stdlib.Counting.mun_card_zero (X := X) hH3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_zero (X := X) hH3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_zero (X := X) hH3) | (have h := (Parley.Items.Stdlib.Counting.mun_card_zero (X := X) hH3); parley_set_side)
  -- 2. axi:excluded-middle P := j = 0
  have s2 : j = 0 ∨ j ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j = 0)); parley_set_side)
  -- 3. cases, from 2
  have s3 : (F.ncard : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. mun:empty-subset
      have s3_1 : ∅ ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_empty_subset (X := X)) | exact ((Parley.Items.Stdlib.Sets.mun_empty_subset (X := X))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_empty_subset (X := X)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_empty_subset (X := X)) | (have h := (Parley.Items.Stdlib.Sets.mun_empty_subset (X := X)); parley_set_side)
      -- 3.2. calculation
      have s3_2 : ((∅ : Set α).ncard : ℤ) = j := by
        calc ((∅ : Set α).ncard : ℤ) = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty) | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty).symm | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side)
          _ = j := by parley_set_side
      -- 3.3. def:part-builder u := ∅, from D1, 3.1, 3.2
      have s3_3 : ∅ ∈ F := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := ∅))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := ∅))).mpr (by parley_set_side); parley_set_side)
      -- 3.4. proof
      have s3_4 : ∀ R ∈ F, R ∈ ({∅} : Set (Set α)) := by
        intro R hK1
        -- 3.4.1. def:part-builder u := R, from D1, K1
        have s3_4_1 : R ⊆ X := by
          try simp only [hD1] at *
          try push_cast at *
          first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).1; parley_set_side)
        -- 3.4.2. substitute X = ∅ (line 1) into line 3.4.1
        have s3_4_2 : R ⊆ ∅ := by parley_subst_at s1 s3_4_1
        -- 3.4.3. mun:subset-empty, from 3.4.2
        have s3_4_3 : R = ∅ := by first | exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side); parley_set_side)
        -- 3.4.4. def:singleton x := R, a := ∅, from 3.4.3
        have s3_4_4 : R ∈ ({∅} : Set (Set α)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_singleton (a := (∅ : Set α)) (x := R))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_singleton (a := (∅ : Set α)) (x := R))).mpr (by parley_set_side); parley_set_side)
        all_goals exact s3_4_4
      -- 3.5. def:subset, from 3.4
      have s3_5 : F ⊆ ({∅} : Set (Set α)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := F) (Y := ({∅} : Set (Set α))))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := F) (Y := ({∅} : Set (Set α))))).mpr (by parley_set_side); parley_set_side)
      -- 3.6. mun:singleton-subset, from 3.3
      have s3_6 : ({∅} : Set (Set α)) ⊆ F := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := F) (a := (∅ : Set α)) s3_3) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_subset (X := F) (a := (∅ : Set α)) s3_3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := F) (a := (∅ : Set α)) s3_3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := F) (a := (∅ : Set α)) s3_3) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := F) (a := (∅ : Set α)) s3_3); parley_set_side)
      -- 3.7. mun:subset-antisymmetric, from 3.5, 3.6
      have s3_7 : F = ({∅} : Set (Set α)) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F) (Y := ({∅} : Set (Set α))) s3_5 s3_6) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F) (Y := ({∅} : Set (Set α))) s3_5 s3_6)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F) (Y := ({∅} : Set (Set α))) s3_5 s3_6) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F) (Y := ({∅} : Set (Set α))) s3_5 s3_6) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F) (Y := ({∅} : Set (Set α))) s3_5 s3_6); parley_set_side)
      -- 3.8. calculation
      have s3_8 : (F.ncard : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by
        calc (F.ncard : ℤ) = (({∅} : Set (Set α)).ncard : ℤ) := by parley_subst s3_7
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α)))) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α)))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α))); parley_set_side)
          _ = (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)); parley_set_side)
          _ = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by parley_subst hC1
      all_goals parley_set_side
    · skip
      -- 3.9. proof
      have s3_9 : ∀ R ∈ 𝒫 X, (R.ncard : ℤ) ≠ j := by
        intro R hK2
        by_contra hc_hS1
        have hS1 : (R.ncard : ℤ) = j := by parley_suppose hc_hS1
        -- 3.9.1. substitute X = ∅ (line 1) into K2
        have s3_9_1 : R ⊆ ∅ := by parley_subst_at s1 hK2
        -- 3.9.2. mun:subset-empty, from 3.9.1
        have s3_9_2 : R = ∅ := by first | exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp (by parley_set_side); parley_set_side)
        -- 3.9.3. calculation
        have s3_9_3 : j = 0 := by
          calc j = (R.ncard : ℤ) := by parley_set_side
            _ = ((∅ : Set α).ncard : ℤ) := by parley_subst s3_9_2
            _ = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty) | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty).symm | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side)
        -- 3.9.4. restate C2
        have s3_9_4 : j ≠ 0 := by parley_set_side
        all_goals parley_set_side
      -- 3.10. mun:part-builder-empty, from D1, 3.9
      have s3_10 : F = ∅ := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.mun_part_builder_empty (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_part_builder_empty (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X))).mpr (by parley_set_side); parley_set_side)
      -- 3.11. contradiction
      have s3_11 : ¬ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ) := by
        by_contra hc_hS2
        have hS2 : j ∈ Finset.Icc (0 : ℤ) (0 : ℤ) := by parley_suppose hc_hS2
        -- 3.11.1. mun:range-bounds a := 0, b := 0, k := j, from S2
        have s3_11_1 : j ≤ 0 := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2); parley_set_side)
        -- 3.11.2. mun:range-bounds a := 0, b := 0, k := j, from S2
        have s3_11_2 : 0 ≤ j := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2); parley_set_side)
        -- 3.11.3. antisymmetry, from 3.11.1, 3.11.2
        have s3_11_3 : j = 0 := by parley_set_side
        -- 3.11.4. restate C2
        have s3_11_4 : j ≠ 0 := by parley_set_side
        all_goals parley_set_side
      -- 3.12. calculation
      have s3_12 : (F.ncard : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by
        calc (F.ncard : ℤ) = ((∅ : Set (Set α)).ncard : ℤ) := by parley_subst s3_10
          _ = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty) | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty).symm | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side)
          _ = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11); parley_set_side)
      all_goals parley_set_side
  -- 4. substitute F = {S ⊆ X : |S| = j} (D1) into line 3
  have s4 : ({S ∈ 𝒫 X | (S.ncard : ℤ) = j}.ncard : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by parley_subst_at hD1 s3
  all_goals exact s4

end Parley.Proofs.Wiedijk.Combinations.ChooseFromNone
