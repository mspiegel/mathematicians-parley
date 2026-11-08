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

/-! Written from proofs/hammack/subset-and-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SubsetAndIntersection.SubsetIffIntersection

set_option maxHeartbeats 400000 in
theorem subset_iff_intersection {α : Type*} (A : Set α) (B : Set α) :
    (A ⊆ B ↔ A ∩ B = A) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ t ∈ A ∩ B, t ∈ A := by
      intro t hK1
      -- 1.1. def:intersection u := t, Y := A, Z := B, from K1
      exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp hK1).1
    -- 2. def:subset, from 1
    have s2 : A ∩ B ⊆ A := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr s1
    -- 3. proof
    have s3 : ∀ t ∈ A, t ∈ A ∩ B := by
      intro t hK2
      -- 3.1. mun:in-subset X := A, Y := B, u := t, from D1, K2
      have s3_1 : t ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2)
      -- 3.2. def:intersection u := t, Y := A, Z := B, from K2, 3.1
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr (by parley_set_side)
    -- 4. def:subset, from 3
    have s4 : A ⊆ A ∩ B := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∩ B))).mpr s3
    -- 5. mun:subset-antisymmetric, from 2, 4
    exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B) (Y := A) s2 s4)
  · skip
    intro hD2
    -- 6. proof
    have s6 : ∀ t ∈ A, t ∈ B := by
      intro t hK3
      -- 6.1. substitute A ∩ B = A (D2) into K3
      have s6_1 : t ∈ A ∩ B := by parley_subst_at hD2 hK3
      -- 6.2. def:intersection u := t, Y := A, Z := B, from 6.1
      exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp s6_1).2
    -- 7. def:subset, from 6
    exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr s6

end Parley.Proofs.Hammack.SubsetAndIntersection.SubsetIffIntersection
