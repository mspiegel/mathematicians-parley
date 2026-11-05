module

public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Proofs.Wiedijk.Ramsey
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ramsey.OnePointPart

theorem one_point_part {α : Type*} (X : Set α) (G : Set (Set α)) (hH2 : X.Finite) (hH3 : ((1 : ℕ) : ℕ∞) ≤ X.encard) :
    (∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ G)) := by
  -- 1. inequalities, from H3
  have r61_1 : 0 ≤ (X.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2); parley_set_side)
  have s1 : ((0 : ℕ) : ℕ∞) < X.encard := by parley_count_int; (parley_order)
  -- 2. mun:card-positive, from 1
  have s2 : ¬ X = ∅ := by first | exact (Parley.Items.Stdlib.Counting.mun_card_positive (X := X) s1) | exact ((Parley.Items.Stdlib.Counting.mun_card_positive (X := X) s1)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_positive (X := X) s1) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_positive (X := X) s1) | (have h := (Parley.Items.Stdlib.Counting.mun_card_positive (X := X) s1); parley_set_side)
  -- 3. obtain v: mun:nonempty-member, from 2
  obtain ⟨v, s3, _⟩ := (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := X) s2)
  -- 4. mun:singleton-subset, from 3
  have s4 : ({v} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) s3) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) s3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) s3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) s3) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) s3); parley_set_side)
  -- 5. mun:card-singleton x := v
  have s5 : ({v} : Set α).encard = ((1 : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v))) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_singleton (x := v))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v)); parley_set_side)
  -- 6. proof
  have s6 : ∀ Y ∈ 𝒫 ({v} : Set α), Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ G := by
    intro Y hK1
    intro hK2
    -- 6.1. mun:card-subset A := Y, B := {v}, from K1
    have s6_1 : Y.encard ≤ ({v} : Set α).encard := by first | exact (Parley.Items.Stdlib.Counting.mun_card_subset (A := Y) (B := ({v} : Set α)) hK1) | exact ((Parley.Items.Stdlib.Counting.mun_card_subset (A := Y) (B := ({v} : Set α)) hK1)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_subset (A := Y) (B := ({v} : Set α)) hK1) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_subset (A := Y) (B := ({v} : Set α)) hK1) | (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := Y) (B := ({v} : Set α)) hK1); parley_set_side)
    -- 6.2. substitute |{v}| = 1 (line 5) into line 6.1
    have s6_2 : Y.encard ≤ ((1 : ℕ) : ℕ∞) := by parley_subst_at s5 s6_1
    -- 6.3. substitute |Y| = 2 (K2) into line 6.2
    have s6_3 : (2 : ℤ) ≤ 1 := by parley_subst_at hK2 s6_2
    exact absurd s6_3 (by norm_num)
    all_goals parley_set_side
  -- 7. inequalities
  have s7 : ((1 : ℕ) : ℕ∞) ≤ ({v} : Set α).encard := by parley_count_int; (parley_order)
  -- 8. D1, from 6, 7
  have s8 : ((1 : ℕ) : ℕ∞) ≤ ({v} : Set α).encard ∧ (∀ Y ∈ 𝒫 ({v} : Set α), Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ G) := by parley_set_side
  -- 9. exhibit, from 4, 8
  have s9 : ∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ G) := ⟨({v} : Set α), by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
  all_goals exact s9

end Parley.Proofs.Wiedijk.Ramsey.OnePointPart
