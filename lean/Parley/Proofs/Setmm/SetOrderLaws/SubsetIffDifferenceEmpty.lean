module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight

/-! Written from proofs/setmm/set-order-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SetOrderLaws.SubsetIffDifferenceEmpty

theorem subset_iff_difference_empty {α : Type*} (A : Set α) (B : Set α) :
    (A ⊆ B ↔ A \ B = ∅) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ↔ A \ B = ∅ := by
    constructor
    · skip
      intro hD1
      -- 1. mun:difference-shrinks Y := A, X := B, Z := B, from D1
      have s1 : A \ B ⊆ B \ B := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := B) (Y := A) (Z := B) hD1) | exact ((Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := B) (Y := A) (Z := B) hD1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := B) (Y := A) (Z := B) hD1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := B) (Y := A) (Z := B) hD1) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := B) (Y := A) (Z := B) hD1); parley_set_side)
      -- 2. substitute
      have s2 : A \ B ⊆ ∅ := by
        have c1 : B \ B = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_self (Y := B)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_self (Y := B))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_self (Y := B)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_self (Y := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_self (Y := B)); parley_set_side)
        have row1 : A \ B ⊆ ∅ := by parley_subst_at c1 s1
        exact row1
      -- 3. mun:subset-empty Y := A ∖ B, from 2
      have s3 : A \ B = ∅ := by first | exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 4. mun:union-difference Y := B, Z := A
      have s4 : B ∪ A \ B = B ∪ A := by first | exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)) | exact ((Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)); parley_set_side)
      -- 5. substitute A ∖ B = ∅ (D2) into line 4
      have s5 : B ∪ ∅ = B ∪ A := by parley_subst_at hD2 s4
      -- 6. calculation
      have s6 : B = B ∪ A := by
        calc B = B ∪ ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_union_empty (Y := B)) | exact ((Parley.Items.Stdlib.Sets.mun_union_empty (Y := B))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_empty (Y := B)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_empty (Y := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_empty (Y := B)); parley_set_side)
          _ = B ∪ A := by parley_set_side
      -- 7. thm:subset-of-union-right
      have s7 : A ⊆ B ∪ A := by first | exact (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := A) (B := B)) | exact ((Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := A) (B := B))).symm | simpa using (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := A) (B := B)) | exact_mod_cast (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := A) (B := B)) | (have h := (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := A) (B := B)); parley_set_side)
      -- 8. substitute B = B ∪ A (line 6) into line 7
      have s8 : A ⊆ B := by parley_subst_at s6 s7
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.SetOrderLaws.SubsetIffDifferenceEmpty
