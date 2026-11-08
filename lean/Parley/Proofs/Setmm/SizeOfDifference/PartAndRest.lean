module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/size-of-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeOfDifference.PartAndRest

theorem part_and_rest {α : Type*} (A : Set α) (B : Set α) (hH3 : B ⊆ A) :
    B ∪ A \ B = A := by
  -- 1. mun:difference-subset X := A, Y := B
  have s1 : A \ B ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B))
  -- 2. mun:union-subset X := B, Y := A ∖ B, Z := A, from H3, 1
  have s2 : B ∪ A \ B ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := A \ B) (Z := A) hH3 s1)
  -- 3. proof
  have s3 : ∀ u ∈ A, u ∈ B ∪ A \ B := by
    intro u hK
    -- 3.1. axi:excluded-middle P := u ∈ B
    have s3_1 : u ∈ B ∨ ¬ u ∈ B := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B))
    -- 3.2. cases, from 3.1
    rcases s3_1 with hC1 | hC2
    · skip
      -- 3.2.1. mun:in-union-left Y := B, Z := A ∖ B, from C1
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := A \ B) (u := u) hC1)
    · skip
      -- 3.2.2. def:difference Y := A, Z := B, from C2, K
      have s3_2_2 : u ∈ A \ B := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_set_side)
      -- 3.2.3. mun:in-union-right Y := B, Z := A ∖ B, from 3.2.2
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A \ B) (u := u) s3_2_2)
  -- 4. def:subset X := A, Y := B ∪ (A ∖ B), from 3
  have s4 : A ⊆ B ∪ A \ B := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A \ B))).mpr s3
  -- 5. mun:subset-antisymmetric X := B ∪ (A ∖ B), Y := A, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B ∪ A \ B) (Y := A) s2 s4)

end Parley.Proofs.Setmm.SizeOfDifference.PartAndRest
