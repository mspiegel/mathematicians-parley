module

public import ZF
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/halmos/union-exists.proof by parley build lean. -/

public section

namespace Parley.Proofs.Halmos.UnionExists.UnionExists

theorem union_exists {α : Type*} [LeanBridges.ZF.Sets α] (A : Set α) (hA_set : LeanBridges.ZF.IsSet A) (B : Set α) (hB_set : LeanBridges.ZF.IsSet B) :
    LeanBridges.ZF.IsSet (A ∪ B) := by
  -- 1. axi:pairing a := A, b := B
  have s1 : LeanBridges.ZF.IsSet ({A, B} : Set (Set α)) := by exact (Parley.Items.Stdlib.Sets.axi_pairing (a := A) hA_set (b := B) hB_set)
  -- 2. axi:unions C := {A, B}, from 1
  have s2 : LeanBridges.ZF.IsSet (⋃ X ∈ ({A, B} : Set (Set α)), X) := by exact (Parley.Items.Stdlib.Sets.axi_unions (C := ({A, B} : Set (Set α))) s1)
  -- 3. proof
  have s3 : ∀ x ∈ (⋃ X ∈ ({A, B} : Set (Set α)), X), x ∈ A ∪ B := by
    intro x hK1
    -- 3.1. def:indexed-union u := x, D := {A, B}, from K1
    have s3_1 : ∃ X ∈ ({A, B} : Set (Set α)), x ∈ X := by exact ((Parley.Items.Stdlib.Sets.def_indexed_union (D := ({A, B} : Set (Set α))) (u := x))).mp hK1
    -- 3.2. obtain X from line 3.1
    obtain ⟨X, s3_2a, s3_2b⟩ := s3_1
    -- 3.3. def:pair x := X, u := A, w := B, from 3.2
    have s3_3 : X = A ∨ X = B := by exact ((Parley.Items.Stdlib.Sets.def_pair (u := A) (w := B) (x := X))).mp s3_2a
    -- 3.4. cases, from 3.3
    rcases s3_3 with hC1 | hC2
    · skip
      -- 3.4.1. substitute X = A (C1) into line 3.2
      have s3_4_1 : x ∈ A := Eq.subst (motive := (fun t : Set α => x ∈ t)) hC1 s3_2b
      -- 3.4.2. mun:in-union-left u := x, Y := A, Z := B, from 3.4.1
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := x) s3_4_1)
    · skip
      -- 3.4.3. substitute X = B (C2) into line 3.2
      have s3_4_3 : x ∈ B := Eq.subst (motive := (fun t : Set α => x ∈ t)) hC2 s3_2b
      -- 3.4.4. mun:in-union-right u := x, Y := A, Z := B, from 3.4.3
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := x) s3_4_3)
  -- 4. proof
  have s4 : ∀ x ∈ A ∪ B, x ∈ (⋃ X ∈ ({A, B} : Set (Set α)), X) := by
    intro x hK2
    -- 4.1. def:union u := x, Y := A, Z := B, from K2
    have s4_1 : x ∈ A ∨ x ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := x))).mp hK2
    -- 4.2. cases, from 4.1
    rcases s4_1 with hC3 | hC4
    · skip
      -- 4.2.1. inspection
      have s4_2_1 : A ∈ ({A, B} : Set (Set α)) := by simp
      -- 4.2.2. exhibit, from C3, 4.2.1
      have s4_2_2 : ∃ X ∈ ({A, B} : Set (Set α)), x ∈ X := ⟨A, s4_2_1, hC3⟩
      -- 4.2.3. def:indexed-union u := x, D := {A, B}, from 4.2.2
      exact ((Parley.Items.Stdlib.Sets.def_indexed_union (D := ({A, B} : Set (Set α))) (u := x))).mpr s4_2_2
    · skip
      -- 4.2.4. inspection
      have s4_2_4 : B ∈ ({A, B} : Set (Set α)) := by simp
      -- 4.2.5. exhibit, from C4, 4.2.4
      have s4_2_5 : ∃ X ∈ ({A, B} : Set (Set α)), x ∈ X := ⟨B, s4_2_4, hC4⟩
      -- 4.2.6. def:indexed-union u := x, D := {A, B}, from 4.2.5
      exact ((Parley.Items.Stdlib.Sets.def_indexed_union (D := ({A, B} : Set (Set α))) (u := x))).mpr s4_2_5
  -- 5. substitute
  have c1 : (⋃ X ∈ ({A, B} : Set (Set α)), X) = A ∪ B := by exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := ⋃ X ∈ ({A, B} : Set (Set α)), X) (Y := A ∪ B) s3 s4)
  have row1 : LeanBridges.ZF.IsSet (A ∪ B) := Eq.subst (motive := (fun t : Set α => LeanBridges.ZF.IsSet t)) c1 s2
  exact row1

end Parley.Proofs.Halmos.UnionExists.UnionExists
