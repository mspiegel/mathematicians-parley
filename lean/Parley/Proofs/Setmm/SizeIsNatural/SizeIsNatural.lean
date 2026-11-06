module

public import ArithTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/size-is-natural.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeIsNatural.SizeIsNatural

theorem size_is_natural {α : Type*} (A : Set α) (hH2 : A.Finite) :
    (0 < (A.ncard : ℤ) ↔ ¬ A = ∅) := by
  -- the theorem. both directions
  have sThm : 0 < (A.ncard : ℤ) ↔ ¬ A = ∅ := by
    constructor
    · skip
      intro hC1
      by_contra hc_hS1
      have hS1 : A = ∅ := by parley_suppose hc_hS1
      -- 1. calculation
      have s1 : A.encard = ((0 : ℕ) : ℕ∞) := by parley_count_after (by
        calc (A.ncard : ℤ) = ((∅ : Set α).ncard : ℤ) := by parley_subst hS1
          _ = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty) | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty).symm | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side))
      -- 2. arithmetic
      have s2 : ¬ (0 : ℤ) < 0 := by parley_arith
      -- 3. substitute |A| = 0 (line 1) into line 2
      have s3 : ¬ 0 < (A.ncard : ℤ) := by parley_count_int; (first | parley_subst_at s1 s2 | (have e_nat : A.ncard = 0 := by exact_mod_cast s1; parley_subst_at e_nat s2))
      all_goals parley_set_side
    · skip
      intro hC2
      -- 4. mun:card-nat0, from H2
      have s4 : 0 ≤ (A.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2); parley_set_side)
      -- 5. contradiction
      have s5 : ¬ A.encard = ((0 : ℕ) : ℕ∞) := by
        by_contra hc_hS2
        have hS2 : A.encard = ((0 : ℕ) : ℕ∞) := by parley_suppose hc_hS2
        -- 5.1. mun:card-zero X := A, from S2
        have s5_1 : A = ∅ := by first | exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := A) hS2) | exact ((Parley.Items.Stdlib.Counting.mun_card_zero (X := A) hS2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_zero (X := A) hS2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_zero (X := A) hS2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_zero (X := A) hS2); parley_set_side)
        -- 5.2. restate C2
        have s5_2 : ¬ A = ∅ := by parley_set_side
        all_goals parley_set_side
      -- 6. mun:nat0-nonzero m := |A|, from 4, 5
      have s6 : 0 < (A.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (A.ncard : ℤ)) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (A.ncard : ℤ)) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (A.ncard : ℤ)) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (A.ncard : ℤ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (A.ncard : ℤ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.SizeIsNatural.SizeIsNatural
