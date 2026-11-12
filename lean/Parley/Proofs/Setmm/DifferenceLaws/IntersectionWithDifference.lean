module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceLaws.IntersectionWithDifference

theorem intersection_with_difference {α : Type*} (A : Set α) (B : Set α) :
    A ∩ (A \ B) = A \ B := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ (A \ B), u ∈ A \ B := by
    intro u hK1
    -- 1.1. def:intersection, from K1
    have s1_1 : u ∈ A ∧ u ∈ A \ B := by exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mp hK1
    -- 1.2. restate 1.1
    exact s1_1.2
  -- 2. def:subset, from 1
  have s2 : A ∩ (A \ B) ⊆ A \ B := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ (A \ B)) (Y := A \ B))).mpr s1
  -- 3. proof
  have s3 : ∀ u ∈ A \ B, u ∈ A ∩ (A \ B) := by
    intro u hK2
    -- 3.1. def:difference, from K2
    have s3_1 : u ∈ A ∧ ¬ u ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp hK2
    -- 3.2. join K2, 3.1
    have s3_2 : u ∈ A ∧ u ∈ A \ B := ⟨s3_1.1, hK2⟩
    -- 3.3. def:intersection, from 3.2
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mpr ⟨s3_2.1, s3_2.2⟩
  -- 4. def:subset, from 3
  have s4 : A \ B ⊆ A ∩ (A \ B) := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := A ∩ (A \ B)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ (A \ B)) (Y := A \ B) s2 s4)

end Parley.Proofs.Setmm.DifferenceLaws.IntersectionWithDifference
