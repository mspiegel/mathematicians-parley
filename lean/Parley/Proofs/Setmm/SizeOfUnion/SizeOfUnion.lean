module

public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.SizeOfUnion.UnionSplit

/-! Written from proofs/setmm/size-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeOfUnion.SizeOfUnion

set_option maxHeartbeats 400000 in
theorem size_of_union {α : Type*} (A : Set α) (B : Set α) (hH3 : A.Finite) (hH4 : B.Finite) :
    (A ∪ B).encard ≤ A.encard + B.encard := by
  -- 1. mun:difference-subset X := B, Y := A
  have s1 : B \ A ⊆ B := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := A)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := A)); parley_set_side)
  -- 2. mun:finite-part X := B, Y := B ∖ A, from H4, 1
  have s2 : (B \ A).Finite := by first | exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B \ A) hH4 s1) | exact ((Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B \ A) hH4 s1)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B \ A) hH4 s1) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B \ A) hH4 s1) | (have h := (Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B \ A) hH4 s1); parley_set_side)
  -- 3. mun:card-nat0 X := A, from H3
  have s3 : 0 ≤ (A.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3); parley_set_side)
  -- 4. mun:card-nat0 X := B, from H4
  have s4 : 0 ≤ (B.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4); parley_set_side)
  -- 5. mun:card-nat0 X := B ∖ A, from 2
  have s5 : 0 ≤ ((B \ A).ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B \ A) s2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B \ A) s2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B \ A) s2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B \ A) s2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B \ A) s2); parley_set_side)
  -- 6. mun:card-subset A := B ∖ A, from 1
  have s6 : (B \ A).encard ≤ B.encard := by first | linarith [(Parley.Items.Stdlib.Counting.mun_card_subset (A := B \ A) (B := B) s1)] | (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := B \ A) (B := B) s1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_subset (A := B \ A) (B := B) s1) | (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := B \ A) (B := B) s1); parley_set_side)
  -- 7. proof
  have s7 : ∀ s ∈ B \ A, ¬ s ∈ A := by
    intro s hK
    -- 7.1. def:difference Y := B, Z := A, from K
    have s7_1a : s ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).1; parley_set_side)
    have s7_1b : ¬ s ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2; parley_set_side)
    -- 7.2. restate 7.1
    have s7_2 : ¬ s ∈ A := by parley_set_side
    all_goals exact s7_2
  -- 8. mun:disjoint-empty Y := A, Z := B ∖ A, from 7
  have s8 : A ∩ (B \ A) = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s7) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s7)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s7) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s7) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s7); parley_set_side)
  -- 9. mun:card-disjoint-union X := A, Y := B ∖ A, m := |A|, n := |B ∖ A|, from 3, 5, 8
  have s9 : (A ∪ B \ A).encard = A.encard + (B \ A).encard := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8); parley_set_side)
  -- 10. thm:union-split
  have s10 : A ∪ B \ A = A ∪ B := by first | exact (Parley.Proofs.Setmm.SizeOfUnion.UnionSplit.union_split (A := A) (B := B)) | exact ((Parley.Proofs.Setmm.SizeOfUnion.UnionSplit.union_split (A := A) (B := B))).symm | simpa using (Parley.Proofs.Setmm.SizeOfUnion.UnionSplit.union_split (A := A) (B := B)) | exact_mod_cast (Parley.Proofs.Setmm.SizeOfUnion.UnionSplit.union_split (A := A) (B := B)) | (have h := (Parley.Proofs.Setmm.SizeOfUnion.UnionSplit.union_split (A := A) (B := B)); parley_set_side)
  -- 11. substitute A ∪ (B ∖ A) = A ∪ B (line 10) into line 9
  have s11 : (A ∪ B).encard = A.encard + (B \ A).encard := by parley_subst_at s10 s9
  -- 12. inequalities
  have s12 : A.encard + (B \ A).encard ≤ A.encard + B.encard := by parley_count_int; (parley_order)
  -- 13. calculation
  have s13 : (A ∪ B).encard ≤ A.encard + B.encard := by parley_count_after (by
    calc ((A ∪ B).ncard : ℤ) = (A.ncard : ℤ) + ((B \ A).ncard : ℤ) := by parley_set_side
      _ ≤ (A.ncard : ℤ) + (B.ncard : ℤ) := by parley_set_side)
  all_goals exact s13

end Parley.Proofs.Setmm.SizeOfUnion.SizeOfUnion
