module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion

theorem subset_of_union {α : Type*} (A : Set α) (B : Set α) :
    A ⊆ A ∪ B := by
  -- 1. proof
  have s1 : ∀ u ∈ A, u ∈ A ∪ B := by
    intro u hK1
    -- 1.1. mun:in-union-left, from K1
    exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) hK1)
  -- 2. def:subset, from 1
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∪ B))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∪ B))).mpr s1; parley_set_side)

end Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion
