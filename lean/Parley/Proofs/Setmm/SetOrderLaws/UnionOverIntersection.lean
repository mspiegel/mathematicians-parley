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

/-! Written from proofs/setmm/set-order-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SetOrderLaws.UnionOverIntersection

set_option maxHeartbeats 600000 in
theorem union_over_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∪ B ∩ C, u ∈ (A ∪ B) ∩ (A ∪ C) := by
    intro u hK1
    -- 1.1. def:union, from K1
    have s1_1 : u ∈ A ∨ u ∈ B ∩ C := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B ∩ C) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B ∩ C) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B ∩ C) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B ∩ C) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B ∩ C) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 1.2. cases, from 1.1
    have s1_2 : u ∈ (A ∪ B) ∩ (A ∪ C) := by
      rcases s1_1 with hC1 | hC2
      · skip
        -- 1.2.1. mun:in-union-left, from C1
        have s1_2_1 : u ∈ A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) hC1)
        -- 1.2.2. mun:in-union-left, from C1
        have s1_2_2 : u ∈ A ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := C) (u := u) hC1)
        -- 1.2.3. join 1.2.1, 1.2.2
        have s1_2_3 : u ∈ A ∪ B ∧ u ∈ A ∪ C := by parley_set_side
        -- 1.2.4. def:intersection, from 1.2.3
        have s1_2_4 : u ∈ (A ∪ B) ∩ (A ∪ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mpr (by parley_set_side); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 1.2.5. def:intersection, from C2
        have s1_2_5 : u ∈ B ∧ u ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp (by parley_set_side); parley_set_side)
        -- 1.2.6. mun:in-union-right, from 1.2.5
        have s1_2_6 : u ∈ A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) s1_2_5.1)
        -- 1.2.7. mun:in-union-right, from 1.2.5
        have s1_2_7 : u ∈ A ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := C) (u := u) s1_2_5.2)
        -- 1.2.8. join 1.2.6, 1.2.7
        have s1_2_8 : u ∈ A ∪ B ∧ u ∈ A ∪ C := by parley_set_side
        -- 1.2.9. def:intersection, from 1.2.8
        have s1_2_9 : u ∈ (A ∪ B) ∩ (A ∪ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mpr (by parley_set_side); parley_set_side)
        all_goals parley_set_side
    all_goals exact s1_2
  -- 2. def:subset, from 1
  have s2 : A ∪ B ∩ C ⊆ (A ∪ B) ∩ (A ∪ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∪ B ∩ C) (Y := (A ∪ B) ∩ (A ∪ C)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∪ B ∩ C) (Y := (A ∪ B) ∩ (A ∪ C)))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ u ∈ (A ∪ B) ∩ (A ∪ C), u ∈ A ∪ B ∩ C := by
    intro u hK2
    -- 3.1. def:intersection, from K2
    have s3_1 : u ∈ A ∪ B ∧ u ∈ A ∪ C := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 3.2. def:union, from 3.1
    have s3_2 : u ∈ A ∨ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 3.3. def:union, from 3.1
    have s3_3 : u ∈ A ∨ u ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := C) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := C) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := C) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := C) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := C) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 3.4. axi:excluded-middle P := u ∈ A
    have s3_4 : u ∈ A ∨ ¬ u ∈ A := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A))
    -- 3.5. cases, from 3.4
    have s3_5 : u ∈ A ∪ B ∩ C := by
      rcases s3_4 with hC3 | hC4
      · skip
        -- 3.5.1. mun:in-union-left, from C3
        have s3_5_1 : u ∈ A ∪ B ∩ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B ∩ C) (u := u) hC3)
        all_goals parley_set_side
      · skip
        -- 3.5.2. mun:disjunctive-syllogism-left, from C4, 3.2
        have s3_5_2 : u ∈ B := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ B) s3_2 hC4)
        -- 3.5.3. mun:disjunctive-syllogism-left, from C4, 3.3
        have s3_5_3 : u ∈ C := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ C) s3_3 hC4)
        -- 3.5.4. join 3.5.2, 3.5.3
        have s3_5_4 : u ∈ B ∧ u ∈ C := by parley_set_side
        -- 3.5.5. def:intersection, from 3.5.4
        have s3_5_5 : u ∈ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr (by parley_set_side); parley_set_side)
        -- 3.5.6. mun:in-union-right, from 3.5.5
        have s3_5_6 : u ∈ A ∪ B ∩ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B ∩ C) (u := u) s3_5_5)
        all_goals parley_set_side
    all_goals exact s3_5
  -- 4. def:subset, from 3
  have s4 : (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∪ B) ∩ (A ∪ C)) (Y := A ∪ B ∩ C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∪ B) ∩ (A ∪ C)) (Y := A ∪ B ∩ C))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B ∩ C) (Y := (A ∪ B) ∩ (A ∪ C)) s2 s4)
  all_goals exact s5

end Parley.Proofs.Setmm.SetOrderLaws.UnionOverIntersection
