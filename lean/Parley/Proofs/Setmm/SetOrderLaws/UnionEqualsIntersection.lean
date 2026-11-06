module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft
public import Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight
public import Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion
public import Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight

/-! Written from proofs/setmm/set-order-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SetOrderLaws.UnionEqualsIntersection

set_option maxHeartbeats 400000 in
theorem union_equals_intersection {α : Type*} (A : Set α) (B : Set α) :
    (A ∪ B = A ∩ B ↔ A = B) := by
  -- the theorem. both directions
  have sThm : A ∪ B = A ∩ B ↔ A = B := by
    constructor
    · skip
      intro hD1
      -- 1. thm:subset-of-union
      have s1 : A ⊆ A ∪ B := by first | exact (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := A) (B := B)) | exact ((Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := A) (B := B))).symm | simpa using (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := A) (B := B)) | exact_mod_cast (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := A) (B := B)) | (have h := (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := A) (B := B)); parley_set_side)
      -- 2. substitute A ∪ B = A ∩ B (D1) into line 1
      have s2 : A ⊆ A ∩ B := by parley_subst_at hD1 s1
      -- 3. thm:intersection-subset-right
      have s3 : A ∩ B ⊆ B := by first | exact (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight.intersection_subset_right (A := A) (B := B)) | exact ((Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight.intersection_subset_right (A := A) (B := B))).symm | simpa using (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight.intersection_subset_right (A := A) (B := B)) | exact_mod_cast (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight.intersection_subset_right (A := A) (B := B)) | (have h := (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight.intersection_subset_right (A := A) (B := B)); parley_set_side)
      -- 4. mun:subset-transitive X := A, Y := A ∩ B, Z := B, from 2, 3
      have s4 : A ⊆ B := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := A ∩ B) (Z := B) s2 s3) | exact ((Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := A ∩ B) (Z := B) s2 s3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := A ∩ B) (Z := B) s2 s3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := A ∩ B) (Z := B) s2 s3) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := A ∩ B) (Z := B) s2 s3); parley_set_side)
      -- 5. thm:subset-of-union-right A := B, B := A
      have s5 : B ⊆ A ∪ B := by first | exact (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := B) (B := A)) | exact ((Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := B) (B := A))).symm | simpa using (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := B) (B := A)) | exact_mod_cast (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := B) (B := A)) | (have h := (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := B) (B := A)); parley_set_side)
      -- 6. substitute A ∪ B = A ∩ B (D1) into line 5
      have s6 : B ⊆ A ∩ B := by parley_subst_at hD1 s5
      -- 7. thm:intersection-subset-left
      have s7 : A ∩ B ⊆ A := by first | exact (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft.intersection_subset_left (A := A) (B := B)) | exact ((Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft.intersection_subset_left (A := A) (B := B))).symm | simpa using (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft.intersection_subset_left (A := A) (B := B)) | exact_mod_cast (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft.intersection_subset_left (A := A) (B := B)) | (have h := (Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft.intersection_subset_left (A := A) (B := B)); parley_set_side)
      -- 8. mun:subset-transitive X := B, Y := A ∩ B, Z := A, from 6, 7
      have s8 : B ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := B) (Y := A ∩ B) (Z := A) s6 s7) | exact ((Parley.Items.Stdlib.Sets.mun_subset_transitive (X := B) (Y := A ∩ B) (Z := A) s6 s7)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := B) (Y := A ∩ B) (Z := A) s6 s7) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := B) (Y := A ∩ B) (Z := A) s6 s7) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := B) (Y := A ∩ B) (Z := A) s6 s7); parley_set_side)
      -- 9. mun:subset-antisymmetric, from 4, 8
      have s9 : A = B := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A) (Y := B) s4 s8) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A) (Y := B) s4 s8)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A) (Y := B) s4 s8) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A) (Y := B) s4 s8) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A) (Y := B) s4 s8); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 10. calculation
      have s10 : A ∪ B = A ∩ B := by
        calc A ∪ B = A ∪ A := by parley_subst hD2
          _ = A := by first | exact (Parley.Items.Stdlib.Sets.mun_union_self (Y := A)) | exact ((Parley.Items.Stdlib.Sets.mun_union_self (Y := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_self (Y := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_self (Y := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_self (Y := A)); parley_set_side)
          _ = A ∩ A := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)); parley_set_side)
          _ = A ∩ B := by parley_subst hD2
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.SetOrderLaws.UnionEqualsIntersection
