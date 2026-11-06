module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion
public import Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight

/-! Written from proofs/setmm/set-order-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SetOrderLaws.UnionKeepsOrder

theorem union_keeps_order {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ B) :
    A ∪ C ⊆ B ∪ C := by
  -- 1. thm:subset-of-union A := B, B := C
  have s1 : B ⊆ B ∪ C := by first | exact (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := B) (B := C)) | exact ((Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := B) (B := C))).symm | simpa using (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := B) (B := C)) | exact_mod_cast (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := B) (B := C)) | (have h := (Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion.subset_of_union (A := B) (B := C)); parley_set_side)
  -- 2. mun:subset-transitive X := A, Y := B, Z := B ∪ C, from H4, 1
  have s2 : A ⊆ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := B) (Z := B ∪ C) hH4 s1) | exact ((Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := B) (Z := B ∪ C) hH4 s1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := B) (Z := B ∪ C) hH4 s1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := B) (Z := B ∪ C) hH4 s1) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := A) (Y := B) (Z := B ∪ C) hH4 s1); parley_set_side)
  -- 3. thm:subset-of-union-right A := C
  have s3 : C ⊆ B ∪ C := by first | exact (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := C) (B := B)) | exact ((Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := C) (B := B))).symm | simpa using (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := C) (B := B)) | exact_mod_cast (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := C) (B := B)) | (have h := (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := C) (B := B)); parley_set_side)
  -- 4. mun:union-subset X := A, Y := C, Z := B ∪ C, from 2, 3
  have s4 : A ∪ C ⊆ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := C) (Z := B ∪ C) s2 s3) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := C) (Z := B ∪ C) s2 s3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := C) (Z := B ∪ C) s2 s3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := C) (Z := B ∪ C) s2 s3) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := C) (Z := B ∪ C) s2 s3); parley_set_side)
  all_goals exact s4

end Parley.Proofs.Setmm.SetOrderLaws.UnionKeepsOrder
