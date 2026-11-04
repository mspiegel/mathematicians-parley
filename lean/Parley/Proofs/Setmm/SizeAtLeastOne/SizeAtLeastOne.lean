module

public import ArithTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/size-at-least-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne

theorem size_at_least_one {α : Type*} (A : Set α) (hH2 : ¬ A = ∅) :
    ((1 : ℕ) : ℕ∞) ≤ A.encard := by
  -- 1. contradiction
  have s1 : ∃ a ∈ A, True := by
    by_contra hc_hS
    have hS : ¬ (∃ a ∈ A, True) := by parley_suppose hc_hS
    -- 1.1. proof
    have s1_1 : ∀ s ∈ A, ¬ s ∈ A := by
      intro s hK
      by_contra hc_hS2
      have hS2 : s ∈ A := by parley_suppose hc_hS2
      -- 1.1.1. exhibit, from S2
      have s1_1_1 : ∃ a ∈ A, True := ⟨s, by parley_set_side, trivial⟩
      -- 1.1.2. restate S
      have s1_1_2 : ¬ (∃ a ∈ A, True) := by parley_set_side
      all_goals parley_set_side
    -- 1.2. calculation
    have s1_2 : A = ∅ := by
      calc A = A ∩ A := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)); parley_set_side)
        _ = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := A) s1_1) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := A) s1_1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := A) s1_1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := A) s1_1) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := A) s1_1); parley_set_side)
    -- 1.3. restate H2
    have s1_3 : ¬ A = ∅ := by parley_set_side
    all_goals parley_set_side
  -- 2. obtain a from line 1
  obtain ⟨a, s2, _⟩ := s1
  -- 3. mun:singleton-subset, from 2
  have s3 : ({a} : Set α) ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := a) s2) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := a) s2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := a) s2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := a) s2) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := a) s2); parley_set_side)
  -- 4. mun:card-subset A := {a}, B := A, from 3
  have s4 : ((({a} : Set α).ncard : ℕ) : ℕ∞) ≤ A.encard := by first | exact (Parley.Items.Stdlib.Counting.mun_card_subset (A := ({a} : Set α)) (B := A) s3) | exact ((Parley.Items.Stdlib.Counting.mun_card_subset (A := ({a} : Set α)) (B := A) s3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_subset (A := ({a} : Set α)) (B := A) s3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_subset (A := ({a} : Set α)) (B := A) s3) | (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := ({a} : Set α)) (B := A) s3); parley_set_side)
  -- 5. substitute
  have s5 : ((1 : ℕ) : ℕ∞) ≤ A.encard := by
    have c1 : (({a} : Set α).ncard : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_singleton (x := a))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a)); parley_set_side)
    have row1 : ((1 : ℕ) : ℕ∞) ≤ A.encard := by parley_subst_at c1 s4
    exact row1
  all_goals exact s5

end Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne
