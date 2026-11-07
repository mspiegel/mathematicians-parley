module

public import ArithTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/subset-iff-difference-empty.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SubsetIffDifferenceEmpty.SubsetIffDifferenceEmpty

set_option maxHeartbeats 400000 in
theorem subset_iff_difference_empty {α : Type*} (A : Set α) (B : Set α) :
    (A ⊆ B ↔ A \ B = ∅) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ↔ A \ B = ∅ := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ A \ B, t ∈ (∅ : Set α) := by
        intro t hK1
        -- 1.1. def:difference u := t, Y := A, Z := B, from K1
        have s1_1a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1; parley_set_side)
        have s1_1b : ¬ t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2; parley_set_side)
        -- 1.2. mun:in-subset X := A, Y := B, u := t, from D1, 1.1
        have s1_2 : t ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 s1_1a)
        all_goals parley_set_side
      -- 2. def:subset, from 1
      have s2 : A \ B ⊆ ∅ := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := ∅))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := ∅))).mpr (by parley_set_side); parley_set_side)
      -- 3. mun:subset-empty Y := A ∖ B, from 2
      have s3 : A \ B = ∅ := by first | exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := A \ B))).mp (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 4. proof
      have s4 : ∀ t ∈ A, t ∈ B := by
        intro t hK2
        by_contra hc_hS
        have hS : ¬ t ∈ B := by parley_suppose hc_hS
        -- 4.1. def:difference u := t, Y := A, Z := B, from K2, S
        have s4_1 : t ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_set_side); parley_set_side)
        -- 4.2. substitute A ∖ B = ∅ (D2) into line 4.1
        have s4_2 : t ∈ (∅ : Set α) := by parley_subst_at hD2 s4_1
        -- 4.3. inspection
        have s4_3 : ¬ t ∈ (∅ : Set α) := by parley_set_side
        all_goals parley_set_side
      -- 5. def:subset, from 4
      have s5 : A ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Hammack.SubsetIffDifferenceEmpty.SubsetIffDifferenceEmpty
