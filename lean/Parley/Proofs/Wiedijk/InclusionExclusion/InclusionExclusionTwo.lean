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

/-! Written from proofs/wiedijk/inclusion-exclusion.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionTwo

theorem inclusion_exclusion_two {α : Type*} (A : Set α) (B : Set α) (hH3 : A.Finite) (hH4 : B.Finite) :
    ((A ∪ B).ncard : ℤ) = (A.ncard : ℤ) + (B.ncard : ℤ) - ((A ∩ B).ncard : ℤ) := by
  -- 1. mun:difference-subset X := B, Y := A
  have s1 : B \ A ⊆ B := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := A))
  -- 2. mun:finite-part X := B, Y := B ∖ A, from H4, 1
  have s2 : (B \ A).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B \ A) hH4 s1)
  -- 3. mun:intersection-subset Y := A, Z := B
  have s3 : A ∩ B ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B))
  -- 4. mun:finite-part X := A, Y := A ∩ B, from H3, 3
  have s4 : (A ∩ B).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := A) (Y := A ∩ B) hH3 s3)
  -- 5. mun:card-nat0 X := A, from H3
  have s5 : 0 ≤ (A.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3)
  -- 6. mun:card-nat0 X := B ∖ A, from 2
  have s6 : 0 ≤ ((B \ A).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B \ A) s2)
  -- 7. mun:card-nat0 X := A ∩ B, from 4
  have s7 : 0 ≤ ((A ∩ B).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A ∩ B) s4)
  -- 8. mun:disjoint-difference Y := A, Z := B
  have s8 : A ∩ (B \ A) = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_difference (Y := A) (Z := B))
  -- 9. mun:card-disjoint-union X := A, Y := B ∖ A, m := |A|, n := |B ∖ A|, from 5, 6, 8
  have s9 : ((A ∪ B \ A).ncard : ℤ) = (A.ncard : ℤ) + ((B \ A).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s8)
  -- 10. mun:union-difference Y := A, Z := B
  have s10 : A ∪ B \ A = A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := A) (Z := B))
  -- 11. substitute A ∪ (B ∖ A) = A ∪ B (line 10) into line 9
  have s11 : ((A ∪ B).ncard : ℤ) = (A.ncard : ℤ) + ((B \ A).ncard : ℤ) := by parley_subst_at s10 s9
  -- 12. mun:intersection-commutes Y := B, Z := A
  have s12 : B ∩ A = A ∩ B := by exact (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := B) (Z := A))
  -- 13. mun:intersection-and-difference-disjoint Y := B, Z := A
  have s13 : (B ∩ A) ∩ (B \ A) = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_intersection_and_difference_disjoint (Y := B) (Z := A))
  -- 14. substitute B ∩ A = A ∩ B (line 12) into line 13
  have s14 : (A ∩ B) ∩ (B \ A) = ∅ := by parley_subst_at s12 s13
  -- 15. mun:intersection-and-difference Y := B, Z := A
  have s15 : B ∩ A ∪ B \ A = B := by exact (Parley.Items.Stdlib.Sets.mun_intersection_and_difference (Y := B) (Z := A))
  -- 16. substitute B ∩ A = A ∩ B (line 12) into line 15
  have s16 : A ∩ B ∪ B \ A = B := by parley_subst_at s12 s15
  -- 17. mun:card-disjoint-union X := A ∩ B, Y := B ∖ A, m := |A ∩ B|, n := |B ∖ A|, from 6, 7, 14
  have s17 : ((A ∩ B ∪ B \ A).ncard : ℤ) = ((A ∩ B).ncard : ℤ) + ((B \ A).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A ∩ B) (Y := B \ A) (m := ((A ∩ B).ncard : ℤ)) (by parley_set_side) (n := ((B \ A).ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) s14)
  -- 18. substitute (A ∩ B) ∪ (B ∖ A) = B (line 16) into line 17
  have s18 : (B.ncard : ℤ) = ((A ∩ B).ncard : ℤ) + ((B \ A).ncard : ℤ) := by parley_subst_at s16 s17
  -- 19. algebra, from 5, 6, 7, 11, 18
  parley_count_int; (linear_combination (norm := parley_norm) s11 + (-1) * s18)

end Parley.Proofs.Wiedijk.InclusionExclusion.InclusionExclusionTwo
