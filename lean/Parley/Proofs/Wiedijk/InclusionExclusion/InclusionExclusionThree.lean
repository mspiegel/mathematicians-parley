module

public import NormTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionTwo

/-! Written from proofs/wiedijk/inclusion-exclusion.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionThree

set_option maxHeartbeats 400000 in
theorem inclusion_exclusion_three {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A.Finite) (hH5 : B.Finite) (hH6 : C.Finite) :
    (((A ∪ B) ∪ C).ncard : ℤ) = (A.ncard : ℤ) + (B.ncard : ℤ) + (C.ncard : ℤ) - ((A ∩ B).ncard : ℤ) - ((A ∩ C).ncard : ℤ) - ((B ∩ C).ncard : ℤ) + (((A ∩ B) ∩ C).ncard : ℤ) := by
  -- 1. mun:union-finite X := A, Y := B, from H4, H5
  have s1 : (A ∪ B).Finite := by exact (Parley.Items.Stdlib.Counting.mun_union_finite (X := A) (Y := B) hH4 hH5)
  -- 2. thm:inclusion-exclusion-two A := A ∪ B, B := C, from H6, 1
  have s2 : (((A ∪ B) ∪ C).ncard : ℤ) = ((A ∪ B).ncard : ℤ) + (C.ncard : ℤ) - (((A ∪ B) ∩ C).ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionTwo.inclusion_exclusion_two (A := A ∪ B) (B := C) s1 hH6)
  -- 3. thm:inclusion-exclusion-two, from H4, H5
  have s3 : ((A ∪ B).ncard : ℤ) = (A.ncard : ℤ) + (B.ncard : ℤ) - ((A ∩ B).ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionTwo.inclusion_exclusion_two (A := A) (B := B) hH4 hH5)
  -- 4. mun:intersection-subset Y := A, Z := C
  have s4 : A ∩ C ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := C))
  -- 5. mun:finite-part X := A, Y := A ∩ C, from H4, 4
  have s5 : (A ∩ C).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A ∩ C) hH4 s4)
  -- 6. mun:intersection-subset Y := B, Z := C
  have s6 : B ∩ C ⊆ B := by exact (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := B) (Z := C))
  -- 7. mun:finite-part X := B, Y := B ∩ C, from H5, 6
  have s7 : (B ∩ C).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B ∩ C) hH5 s6)
  -- 8. thm:inclusion-exclusion-two A := A ∩ C, B := B ∩ C, from 5, 7
  have s8 : ((A ∩ C ∪ B ∩ C).ncard : ℤ) = ((A ∩ C).ncard : ℤ) + ((B ∩ C).ncard : ℤ) - (((A ∩ C) ∩ (B ∩ C)).ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionTwo.inclusion_exclusion_two (A := A ∩ C) (B := B ∩ C) s5 s7)
  -- 9. substitute
  have s9 : (((A ∪ B) ∩ C).ncard : ℤ) = ((A ∩ C).ncard : ℤ) + ((B ∩ C).ncard : ℤ) - (((A ∩ C) ∩ (B ∩ C)).ncard : ℤ) := by
    have c1 : A ∩ C ∪ B ∩ C = (A ∪ B) ∩ C := (Parley.Items.Stdlib.Sets.mun_intersection_distributes_right (X := A) (Y := B) (Z := C)).symm
    have row1 : (((A ∪ B) ∩ C).ncard : ℤ) = ((A ∩ C).ncard : ℤ) + ((B ∩ C).ncard : ℤ) - (((A ∩ C) ∩ (B ∩ C)).ncard : ℤ) := by parley_subst_at c1 s8
    exact row1
  -- 10. substitute
  have s10 : (((A ∪ B) ∩ C).ncard : ℤ) = ((A ∩ C).ncard : ℤ) + ((B ∩ C).ncard : ℤ) - (((A ∩ B) ∩ C).ncard : ℤ) := by
    have c1 : (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := (Parley.Items.Stdlib.Sets.mun_intersection_distributes_over_intersection (X := A) (Y := B) (Z := C)).symm
    have row1 : (((A ∪ B) ∩ C).ncard : ℤ) = ((A ∩ C).ncard : ℤ) + ((B ∩ C).ncard : ℤ) - (((A ∩ B) ∩ C).ncard : ℤ) := by parley_subst_at c1 s9
    exact row1
  -- 11. mun:intersection-subset Y := A, Z := B
  have s11 : A ∩ B ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B))
  -- 12. mun:finite-part X := A, Y := A ∩ B, from H4, 11
  have s12 : (A ∩ B).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A ∩ B) hH4 s11)
  -- 13. mun:intersection-subset Y := A ∩ B, Z := C
  have s13 : (A ∩ B) ∩ C ⊆ A ∩ B := by exact (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A ∩ B) (Z := C))
  -- 14. mun:finite-part X := A ∩ B, Y := A ∩ B ∩ C, from 12, 13
  have s14 : ((A ∩ B) ∩ C).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := A ∩ B) (Y := (A ∩ B) ∩ C) s12 s13)
  -- 15. algebra, from 2, 3, 10
  have r141_1 : 0 ≤ (A.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH4)
  have r141_2 : 0 ≤ (B.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH5)
  have r141_3 : 0 ≤ (C.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := C) hH6)
  have r141_4 : 0 ≤ ((A ∩ B).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A ∩ B) s12)
  have r141_5 : 0 ≤ ((A ∩ C).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A ∩ C) s5)
  have r141_6 : 0 ≤ ((B ∩ C).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B ∩ C) s7)
  have r141_7 : 0 ≤ (((A ∩ B) ∩ C).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := (A ∩ B) ∩ C) s14)
  linear_combination (norm := parley_norm) s2 + s3 + (-1) * s10

end Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionThree
