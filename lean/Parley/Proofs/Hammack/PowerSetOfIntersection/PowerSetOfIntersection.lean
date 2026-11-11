module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/power-set-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PowerSetOfIntersection.PowerSetOfIntersection

theorem power_set_of_intersection {α : Type*} (A : Set α) (B : Set α) :
    𝒫 A ∩ 𝒫 B = 𝒫 (A ∩ B) := by
  -- 1. proof
  have s1 : ∀ t ∈ 𝒫 A ∩ 𝒫 B, t ∈ 𝒫 (A ∩ B) := by
    intro t hK1
    -- 1.1. def:intersection u := t, Y := 𝒫A, Z := 𝒫B, from K1
    have s1_1a : t ∈ 𝒫 A := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp hK1).1
    have s1_1b : t ∈ 𝒫 B := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp hK1).2
    -- 1.2. def:powerset S := t, from 1.1
    have s1_2 : t ⊆ A := by exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp s1_1a
    -- 1.3. def:powerset S := t, A := B, from 1.1
    have s1_3 : t ⊆ B := by exact ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mp s1_1b
    -- 1.4. proof
    have s1_4 : ∀ x ∈ t, x ∈ A ∩ B := by
      intro x hK2
      -- 1.4.1. mun:in-subset X := t, Y := A, u := x, from K2, 1.2
      have s1_4_1 : x ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) s1_2 hK2)
      -- 1.4.2. mun:in-subset X := t, Y := B, u := x, from K2, 1.3
      have s1_4_2 : x ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := B) (u := x) s1_3 hK2)
      -- 1.4.3. def:intersection u := x, Y := A, Z := B, from 1.4.1, 1.4.2
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mpr ⟨s1_4_1, s1_4_2⟩
    -- 1.5. def:subset, from 1.4
    have s1_5 : t ⊆ A ∩ B := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A ∩ B))).mpr s1_4
    -- 1.6. def:powerset S := t, A := A ∩ B, from 1.5
    exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mpr s1_5
  -- 2. def:subset, from 1
  have s2 : 𝒫 A ∩ 𝒫 B ⊆ 𝒫 (A ∩ B) := ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)))).mpr s1
  -- 3. proof
  have s3 : ∀ t ∈ 𝒫 (A ∩ B), t ∈ 𝒫 A ∩ 𝒫 B := by
    intro t hK3
    -- 3.1. def:powerset S := t, A := A ∩ B, from K3
    have s3_1 : t ⊆ A ∩ B := by exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A ∩ B) (S := t))).mp hK3
    -- 3.2. proof
    have s3_2 : ∀ x ∈ t, x ∈ A := by
      intro x hK4
      -- 3.2.1. mun:in-subset X := t, Y := A ∩ B, u := x, from K4, 3.1
      have s3_2_1 : x ∈ A ∩ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) s3_1 hK4)
      -- 3.2.2. def:intersection u := x, Y := A, Z := B, from 3.2.1
      exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp s3_2_1).1
    -- 3.3. proof
    have s3_3 : ∀ x ∈ t, x ∈ B := by
      intro x hK5
      -- 3.3.1. mun:in-subset X := t, Y := A ∩ B, u := x, from K5, 3.1
      have s3_3_1 : x ∈ A ∩ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A ∩ B) (u := x) s3_1 hK5)
      -- 3.3.2. def:intersection u := x, Y := A, Z := B, from 3.3.1
      exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp s3_3_1).2
    -- 3.4. def:subset, from 3.2
    have s3_4 : t ⊆ A := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A))).mpr s3_2
    -- 3.5. def:subset, from 3.3
    have s3_5 : t ⊆ B := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := B))).mpr s3_3
    -- 3.6. def:powerset S := t, from 3.4
    have s3_6 : t ∈ 𝒫 A := ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mpr s3_4
    -- 3.7. def:powerset S := t, A := B, from 3.5
    have s3_7 : t ∈ 𝒫 B := ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := t))).mpr s3_5
    -- 3.8. def:intersection u := t, Y := 𝒫A, Z := 𝒫B, from 3.6, 3.7
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mpr ⟨s3_6, s3_7⟩
  -- 4. def:subset, from 3
  have s4 : 𝒫 (A ∩ B) ⊆ 𝒫 A ∩ 𝒫 B := ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 (A ∩ B)) (Y := 𝒫 A ∩ 𝒫 B))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 A ∩ 𝒫 B) (Y := 𝒫 (A ∩ B)) s2 s4)

end Parley.Proofs.Hammack.PowerSetOfIntersection.PowerSetOfIntersection
