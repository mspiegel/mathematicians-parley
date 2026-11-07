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
  have sThm : A ⊆ B ↔ A ∩ B = A := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ A ∩ B, t ∈ A := by
        intro t hK1
        -- 1.1. def:intersection u := t, Y := A, Z := B, from K1
        have s1_1 : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1; parley_set_side)
        all_goals exact s1_1
      -- 2. def:subset, from 1
      have s2 : A ∩ B ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr (by parley_set_side); parley_set_side)
      -- 3. proof
      have s3 : ∀ t ∈ A, t ∈ A ∩ B := by
        intro t hK2
        -- 3.1. mun:in-subset X := A, Y := B, u := t, from D1, K2
        have s3_1 : t ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2); parley_set_side)
        -- 3.2. def:intersection u := t, Y := A, Z := B, from K2, 3.1
        have s3_2 : t ∈ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr (by parley_set_side); parley_set_side)
        all_goals exact s3_2
      -- 4. def:subset, from 3
      have s4 : A ⊆ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∩ B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∩ B))).mpr (by parley_set_side); parley_set_side)
      -- 5. mun:subset-antisymmetric, from 2, 4
      have s5 : A ∩ B = A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B) (Y := A) s2 s4) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B) (Y := A) s2 s4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B) (Y := A) s2 s4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B) (Y := A) s2 s4) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B) (Y := A) s2 s4); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 6. proof
      have s6 : ∀ t ∈ A, t ∈ B := by
        intro t hK3
        -- 6.1. substitute A ∩ B = A (D2) into K3
        have s6_1 : t ∈ A ∩ B := by parley_subst_at hD2 hK3
        -- 6.2. def:intersection u := t, Y := A, Z := B, from 6.1
        have s6_2 : t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2; parley_set_side)
        all_goals exact s6_2
      -- 7. def:subset, from 6
      have s7 : A ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Hammack.SubsetAndIntersection.SubsetIffIntersection
