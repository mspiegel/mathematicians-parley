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
  constructor
  · skip
    intro hD1
    -- 1. mun:difference-shrinks Y := A, X := B, Z := B, from D1
    have s1 : A \ B ⊆ B \ B := by exact (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := B) (Y := A) (Z := B) hD1)
    -- 2. substitute
    have s2 : A \ B ⊆ ∅ := by
      have c1 : B \ B = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_difference_self (Y := B))
      have row1 : A \ B ⊆ ∅ := by parley_subst_at c1 s1
      exact row1
    -- 3. mun:subset-empty Y := A ∖ B, from 2
    exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp s2
  · skip
    intro hD2
    -- 4. mun:union-difference Y := B, Z := A
    have s4 : B ∪ A \ B = B ∪ A := by exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A))
    -- 5. substitute A ∖ B = ∅ (D2) into line 4
    have s5 : B ∪ ∅ = B ∪ A := by parley_subst_at hD2 s4
    -- 6. calculation
    have s6 : B = B ∪ A := by
      calc B = B ∪ ∅ := by exact (Parley.Items.Stdlib.Sets.mun_union_empty (Y := B)).symm
        _ = B ∪ A := by exact s5
    -- 7. thm:subset-of-union-right
    have s7 : A ⊆ B ∪ A := by exact (Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight.subset_of_union_right (A := A) (B := B))
    -- 8. substitute B = B ∪ A (line 6) into line 7
    parley_subst_at s6 s7

end Parley.Proofs.Setmm.SetOrderLaws.SubsetIffDifferenceEmpty
