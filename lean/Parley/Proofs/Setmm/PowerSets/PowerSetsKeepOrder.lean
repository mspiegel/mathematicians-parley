module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself

/-! Written from proofs/setmm/power-sets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerSets.PowerSetsKeepOrder

theorem power_sets_keep_order {α : Type*} (A : Set α) (B : Set α) :
    (A ⊆ B ↔ 𝒫 A ⊆ 𝒫 B) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ↔ 𝒫 A ⊆ 𝒫 B := by
    constructor
    · skip
      intro hD1
      -- 1. mun:powerset-monotone X := B, Y := A, from D1
      have s1 : 𝒫 A ⊆ 𝒫 B := by first | exact (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := B) (Y := A) hD1) | exact ((Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := B) (Y := A) hD1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := B) (Y := A) hD1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := B) (Y := A) hD1) | (have h := (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := B) (Y := A) hD1); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 2. thm:set-is-a-part-of-itself
      have s2 : A ∈ 𝒫 A := by first | exact (Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself.set_is_a_part_of_itself (A := A)) | exact ((Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself.set_is_a_part_of_itself (A := A))).symm | simpa using (Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself.set_is_a_part_of_itself (A := A)) | exact_mod_cast (Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself.set_is_a_part_of_itself (A := A)) | (have h := (Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself.set_is_a_part_of_itself (A := A)); parley_set_side)
      -- 3. mun:in-subset X := 𝒫A, Y := 𝒫B, u := A, from D2, 2
      have s3 : A ∈ 𝒫 B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := 𝒫 A) (Y := 𝒫 B) (u := A) hD2 s2) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := 𝒫 A) (Y := 𝒫 B) (u := A) hD2 s2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := 𝒫 A) (Y := 𝒫 B) (u := A) hD2 s2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := 𝒫 A) (Y := 𝒫 B) (u := A) hD2 s2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := 𝒫 A) (Y := 𝒫 B) (u := A) hD2 s2); parley_set_side)
      -- 4. def:powerset S := A, A := B, from 3
      have s4 : A ⊆ B := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := A))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := A))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := A))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := A))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := B) (S := A))).mp (by parley_set_side); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.PowerSets.PowerSetsKeepOrder
