module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/union-and-difference-equal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.UnionAndDifferenceEqual.UnionAndDifferenceEqual

set_option maxHeartbeats 600000 in
theorem union_and_difference_equal {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ C) (hH5 : A ∩ B = ∅) :
    (A ∪ B = C ↔ C \ A = B) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ u ∈ C \ A, u ∈ B := by
      intro u hK1
      -- 1.1. def:difference Y := C, Z := A, from K1
      have s1_1a : u ∈ C := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp hK1).1
      have s1_1b : ¬ u ∈ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp hK1).2
      -- 1.2. substitute A ∪ B = C (D1) into line 1.1
      have s1_2 : u ∈ A ∪ B := by parley_subst_at hD1 s1_1a
      -- 1.3. def:union Y := A, Z := B, from 1.2
      have s1_3 : u ∈ A ∨ u ∈ B := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp s1_2
      -- 1.4. cases, from 1.3
      rcases s1_3 with hC1 | hC2
      · skip
        -- 1.4.1. restate 1.1
        have s1_4_1 : ¬ u ∈ A := by parley_set_side
        exact absurd hC1 s1_4_1
      · skip
        -- 1.4.2. restate C2
        parley_set_side
    -- 2. def:subset X := C ∖ A, Y := B, from 1
    have s2 : C \ A ⊆ B := ((Parley.Items.Stdlib.Sets.def_subset (X := C \ A) (Y := B))).mpr s1
    -- 3. proof
    have s3 : ∀ u ∈ B, u ∈ C \ A := by
      intro u hK2
      -- 3.1. mun:in-union-right Y := A, Z := B, from K2
      have s3_1 : u ∈ A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) hK2)
      -- 3.2. substitute A ∪ B = C (D1) into line 3.1
      have s3_2 : u ∈ C := by parley_subst_at hD1 s3_1
      -- 3.3. contradiction
      have s3_3 : ¬ u ∈ A := by
        intro hS
        -- 3.3.1. mun:disjoint-member Y := A, Z := B, from H5, S
        have s3_3_1 : ¬ u ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := u) hH5 hS)
        exact s3_3_1 hK2
      -- 3.4. def:difference Y := C, Z := A, from 3.2, 3.3
      exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mpr (by parley_set_side)
    -- 4. def:subset X := B, Y := C ∖ A, from 3
    have s4 : B ⊆ C \ A := ((Parley.Items.Stdlib.Sets.def_subset (X := B) (Y := C \ A))).mpr s3
    -- 5. mun:subset-antisymmetric X := C ∖ A, Y := B, from 2, 4
    exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) s2 s4)
  · skip
    intro hD2
    -- 6. mun:difference-subset X := C, Y := A
    have s6 : C \ A ⊆ C := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := C) (Y := A))
    -- 7. substitute C ∖ A = B (D2) into line 6
    have s7 : B ⊆ C := by parley_subst_at hD2 s6
    -- 8. mun:union-subset X := A, Y := B, Z := C, from H4, 7
    have s8 : A ∪ B ⊆ C := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := B) (Z := C) hH4 s7)
    -- 9. proof
    have s9 : ∀ u ∈ C, u ∈ A ∪ B := by
      intro u hK3
      -- 9.1. axi:excluded-middle P := u ∈ A
      have s9_1 : u ∈ A ∨ ¬ u ∈ A := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A))
      -- 9.2. cases, from 9.1
      rcases s9_1 with hC3 | hC4
      · skip
        -- 9.2.1. mun:in-union-left Y := A, Z := B, from C3
        exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) hC3)
      · skip
        -- 9.2.2. def:difference Y := C, Z := A, from C4, K3
        have s9_2_2 : u ∈ C \ A := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mpr (by parley_set_side)
        -- 9.2.3. substitute C ∖ A = B (D2) into line 9.2.2
        have s9_2_3 : u ∈ B := by parley_subst_at hD2 s9_2_2
        -- 9.2.4. mun:in-union-right Y := A, Z := B, from 9.2.3
        exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) s9_2_3)
    -- 10. def:subset X := C, Y := A ∪ B, from 9
    have s10 : C ⊆ A ∪ B := ((Parley.Items.Stdlib.Sets.def_subset (X := C) (Y := A ∪ B))).mpr s9
    -- 11. mun:subset-antisymmetric X := A ∪ B, Y := C, from 8, 10
    exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) s8 s10)

end Parley.Proofs.Setmm.UnionAndDifferenceEqual.UnionAndDifferenceEqual
