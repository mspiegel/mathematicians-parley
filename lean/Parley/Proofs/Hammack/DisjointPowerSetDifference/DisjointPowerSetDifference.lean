module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/disjoint-power-set-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DisjointPowerSetDifference.DisjointPowerSetDifference

theorem disjoint_power_set_difference {α : Type*} (A : Set α) (B : Set α) (hH3 : A ∩ B = ∅) :
    𝒫 A \ 𝒫 B ⊆ 𝒫 (A \ B) := by
  -- 1. proof
  have s1 : ∀ t ∈ 𝒫 A \ 𝒫 B, t ∈ 𝒫 (A \ B) := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := 𝒫A, Z := 𝒫B, from K1
    have s1_1a : t ∈ 𝒫 A := (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp hK1).1
    have s1_1b : ¬ t ∈ 𝒫 B := (((Parley.Items.Stdlib.Sets.def_difference (Y := 𝒫 A) (Z := 𝒫 B) (u := t))).mp hK1).2
    -- 1.2. def:powerset S := t, from 1.1
    have s1_2 : t ⊆ A := ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := t))).mp s1_1a
    -- 1.3. proof
    have s1_3 : ∀ x ∈ t, x ∈ A \ B := by
      intro x hK2
      -- 1.3.1. mun:in-subset X := t, Y := A, u := x, from K2, 1.2
      have s1_3_1 : x ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := t) (Y := A) (u := x) s1_2 hK2)
      -- 1.3.2. mun:disjoint-member Y := A, Z := B, u := x, from H3, 1.3.1
      have s1_3_2 : ¬ x ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := x) hH3 s1_3_1)
      -- 1.3.3. def:difference u := x, Y := A, Z := B, from 1.3.1, 1.3.2
      exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := x))).mpr (by parley_set_side)
    -- 1.4. def:subset, from 1.3
    have s1_4 : t ⊆ A \ B := ((Parley.Items.Stdlib.Sets.def_subset (X := t) (Y := A \ B))).mpr s1_3
    -- 1.5. def:powerset S := t, A := A ∖ B, from 1.4
    exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A \ B) (S := t))).mpr s1_4
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 A \ 𝒫 B) (Y := 𝒫 (A \ B)))).mpr s1

end Parley.Proofs.Hammack.DisjointPowerSetDifference.DisjointPowerSetDifference
