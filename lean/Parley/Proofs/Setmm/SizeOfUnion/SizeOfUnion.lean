module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.SizeOfUnion.UnionSplit

/-! Written from proofs/setmm/size-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeOfUnion.SizeOfUnion

theorem size_of_union {α : Type*} (A : Set α) (B : Set α) (hH3 : A.Finite) (hH4 : B.Finite) :
    ((A ∪ B).ncard : ℤ) ≤ (A.ncard : ℤ) + (B.ncard : ℤ) := by
  -- 1. mun:difference-subset X := B, Y := A
  have s1 : B \ A ⊆ B := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := A))
  -- 2. mun:finite-part X := B, Y := B ∖ A, from H4, 1
  have s2 : (B \ A).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := B) (Y := B \ A) hH4 s1)
  -- 3. mun:card-nat0 X := A, from H3
  have s3 : 0 ≤ (A.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3)
  -- 4. mun:card-nat0 X := B, from H4
  have s4 : 0 ≤ (B.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4)
  -- 5. mun:card-nat0 X := B ∖ A, from 2
  have s5 : 0 ≤ ((B \ A).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B \ A) s2)
  -- 6. mun:card-subset A := B ∖ A, from 1
  have s6 : ((B \ A).ncard : ℤ) ≤ (B.ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := B \ A) (B := B) s1); simp only [← Set.Finite.cast_ncard_eq ((s2 : (B \ A : Set α).Finite)), ← Set.Finite.cast_ncard_eq ((hH4 : (B : Set α).Finite))] at h ⊢; exact_mod_cast h)
  -- 7. proof
  have s7 : ∀ s ∈ B \ A, ¬ s ∈ A := by
    intro s hK
    -- 7.1. def:difference Y := B, Z := A, from K
    have s7_1a : s ∈ B := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp hK).1
    have s7_1b : ¬ s ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp hK).2
    -- 7.2. restate 7.1
    exact s7_1b
  -- 8. mun:disjoint-empty Y := A, Z := B ∖ A, from 7
  have s8 : A ∩ (B \ A) = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s7)
  -- 9. mun:card-disjoint-union X := A, Y := B ∖ A, m := |A|, n := |B ∖ A|, from 3, 5, 8
  have s9 : ((A ∪ B \ A).ncard : ℤ) = (A.ncard : ℤ) + ((B \ A).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B \ A) (m := (A.ncard : ℤ)) s3 (n := ((B \ A).ncard : ℤ)) s5 (by rw [Int.toNat_natCast, Set.Finite.cast_ncard_eq ((hH3 : (A : Set α).Finite))]) (by rw [Int.toNat_natCast, Set.Finite.cast_ncard_eq ((s2 : (B \ A : Set α).Finite))]) s8)
  -- 10. thm:union-split
  have s10 : A ∪ B \ A = A ∪ B := by exact (Parley.Proofs.Setmm.SizeOfUnion.UnionSplit.union_split (A := A) (B := B))
  -- 11. substitute A ∪ (B ∖ A) = A ∪ B (line 10) into line 9
  have s11 : ((A ∪ B).ncard : ℤ) = (A.ncard : ℤ) + ((B \ A).ncard : ℤ) := by parley_subst_at s10 s9
  -- 12. inequalities
  have s12 : (A.ncard : ℤ) + ((B \ A).ncard : ℤ) ≤ (A.ncard : ℤ) + (B.ncard : ℤ) := by parley_count_int; (linarith only [s6])
  -- 13. calculation
  parley_count_after (by
    calc ((A ∪ B).ncard : ℤ) = (A.ncard : ℤ) + ((B \ A).ncard : ℤ) := by parley_set_side
      _ ≤ (A.ncard : ℤ) + (B.ncard : ℤ) := by parley_set_side)

end Parley.Proofs.Setmm.SizeOfUnion.SizeOfUnion
