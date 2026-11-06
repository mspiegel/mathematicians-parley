module

public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.SizeOfDifference.PartAndRest

/-! Written from proofs/setmm/size-of-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeOfDifference.SizeOfDifference

set_option maxHeartbeats 400000 in
theorem size_of_difference {α : Type*} (A : Set α) (B : Set α) (hH3 : A.Finite) (hH4 : B ⊆ A) :
    ((A \ B).ncard : ℤ) = (A.ncard : ℤ) - (B.ncard : ℤ) := by
  -- 1. mun:difference-subset X := A, Y := B
  have s1 : A \ B ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)); parley_set_side)
  -- 2. mun:finite-part X := A, Y := A ∖ B, from H3, 1
  have s2 : (A \ B).Finite := by first | exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A \ B) hH3 s1) | exact ((Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A \ B) hH3 s1)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A \ B) hH3 s1) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A \ B) hH3 s1) | (have h := (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A \ B) hH3 s1); parley_set_side)
  -- 3. mun:finite-part X := A, Y := B, from H3, H4
  have s3 : B.Finite := by first | exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := B) hH3 hH4) | exact ((Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := B) hH3 hH4)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := B) hH3 hH4) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := B) hH3 hH4) | (have h := (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := B) hH3 hH4); parley_set_side)
  -- 4. mun:card-nat0 X := B, from 3
  have s4 : 0 ≤ (B.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) s3) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) s3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) s3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) s3) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) s3); parley_set_side)
  -- 5. mun:card-nat0 X := A ∖ B, from 2
  have s5 : 0 ≤ ((A \ B).ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A \ B) s2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A \ B) s2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A \ B) s2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A \ B) s2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A \ B) s2); parley_set_side)
  -- 6. proof
  have s6 : ∀ s ∈ A \ B, ¬ s ∈ B := by
    intro s hK
    -- 6.1. def:difference Y := A, Z := B, from K
    have s6_1a : s ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).1; parley_set_side)
    have s6_1b : ¬ s ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := s))).mp (by parley_set_side)).2; parley_set_side)
    -- 6.2. restate 6.1
    have s6_2 : ¬ s ∈ B := by parley_set_side
    all_goals exact s6_2
  -- 7. mun:disjoint-empty Y := B, Z := A ∖ B, from 6
  have s7 : B ∩ (A \ B) = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A \ B) s6) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A \ B) s6)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A \ B) s6) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A \ B) s6) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A \ B) s6); parley_set_side)
  -- 8. mun:card-disjoint-union X := B, Y := A ∖ B, m := |B|, n := |A ∖ B|, from 4, 5, 7
  have s8 : (B ∪ A \ B).encard = B.encard + (A \ B).encard := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := B) (Y := A \ B) (m := (B.ncard : ℤ)) (by parley_set_side) (n := ((A \ B).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s7); parley_set_side)
  -- 9. substitute
  have s9 : A.encard = B.encard + (A \ B).encard := by parley_count_after (by
    have c1 : B ∪ A \ B = A := by first | exact (Parley.Proofs.Setmm.SizeOfDifference.PartAndRest.part_and_rest (A := A) (B := B) hH4) | exact ((Parley.Proofs.Setmm.SizeOfDifference.PartAndRest.part_and_rest (A := A) (B := B) hH4)).symm | simpa using (Parley.Proofs.Setmm.SizeOfDifference.PartAndRest.part_and_rest (A := A) (B := B) hH4) | exact_mod_cast (Parley.Proofs.Setmm.SizeOfDifference.PartAndRest.part_and_rest (A := A) (B := B) hH4) | (have h := (Parley.Proofs.Setmm.SizeOfDifference.PartAndRest.part_and_rest (A := A) (B := B) hH4); parley_set_side)
    have row1 : A.encard = B.encard + (A \ B).encard := by parley_subst_at c1 s8
    exact row1)
  -- 10. algebra, from 4, 5, 9
  have s10 : ((A \ B).ncard : ℤ) = (A.ncard : ℤ) - (B.ncard : ℤ) := by parley_count_int; (linear_combination (norm := parley_norm) (-1) * s9)
  all_goals exact s10

end Parley.Proofs.Setmm.SizeOfDifference.SizeOfDifference
