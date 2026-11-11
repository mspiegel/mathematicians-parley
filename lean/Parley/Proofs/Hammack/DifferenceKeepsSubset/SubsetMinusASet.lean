module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/difference-keeps-subset.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DifferenceKeepsSubset.SubsetMinusASet

theorem subset_minus_a_set {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ B) :
    A \ C ⊆ B \ C := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ C, t ∈ B \ C := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := C, from K1
    have s1_1a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hK1).1
    have s1_1b : ¬ t ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hK1).2
    -- 1.2. mun:in-subset X := A, Y := B, u := t, from H4, 1.1
    have s1_2 : t ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hH4 s1_1a)
    -- 1.3. def:difference u := t, Y := B, Z := C, from 1.1, 1.2
    exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr ⟨s1_2, s1_1b⟩
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ C) (Y := B \ C))).mpr s1

end Parley.Proofs.Hammack.DifferenceKeepsSubset.SubsetMinusASet
