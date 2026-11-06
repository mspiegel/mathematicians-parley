module

public import AlgebraTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/multiples-of-six.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MultiplesOfSix.MultiplesOfSix

set_option maxHeartbeats 600000 in
theorem multiples_of_six :
    (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ) = (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by
  -- 1. proof
  have s1 : ∀ t ∈ (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ), t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by
    intro t hK1
    -- 1.1. obtain m: def:set-image u := t, from K1
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 6 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 1.2. algebra, from 1.1
    have s1_2 : t = 2 * (3 * m) := by linear_combination (norm := parley_norm) s1_1
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ n : ℤ, t = 2 * n := ⟨3 * m, by parley_set_side⟩
    -- 1.4. def:set-image u := t, from 1.3
    have s1_4 : t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    -- 1.5. algebra, from 1.1
    have s1_5 : t = 3 * (2 * m) := by linear_combination (norm := parley_norm) s1_1
    -- 1.6. exhibit, from 1.5
    have s1_6 : ∃ n : ℤ, t = 3 * n := ⟨2 * m, by parley_set_side⟩
    -- 1.7. def:set-image u := t, from 1.6
    have s1_7 : t ∈ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 3 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 3 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    -- 1.8. def:intersection u := t, from 1.4, 1.7
    have s1_8 : t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_8
  -- 2. def:subset, from 1
  have s2 : (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ), t ∈ (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ) := by
    intro t hK2
    -- 3.1. def:intersection u := t, from K2
    have s3_1 : t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    -- 3.2. def:intersection u := t, from K2
    have s3_2 : t ∈ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 3.3. obtain a: def:set-image u := t, from 3.1
    obtain ⟨a, _, s3_3⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 3.4. obtain b: def:set-image u := t, from 3.2
    obtain ⟨b, _, s3_4⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 3 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 3.5. algebra
    have s3_5 : t = 3 * t - 2 * t := by parley_ring
    -- 3.6. substitute
    have s3_6 : t = 6 * a - 2 * t := by
      have c1 : 3 * t = 6 * a := by linear_combination (norm := parley_norm) (3) * s3_3
      have row1 : t = 6 * a - 2 * t := by parley_subst_at c1 s3_5
      exact row1
    -- 3.7. substitute
    have s3_7 : t = 6 * a - 6 * b := by
      have c1 : 2 * t = 6 * b := by linear_combination (norm := parley_norm) (2) * s3_4
      have row1 : t = 6 * a - 6 * b := by parley_subst_at c1 s3_6
      exact row1
    -- 3.8. calculation
    have s3_8 : t = 6 * (a - b) := by
      calc t = 6 * a - 6 * b := by parley_set_side
        _ = 6 * (a - b) := by parley_ring
    -- 3.9. exhibit, from 3.8
    have s3_9 : ∃ n : ℤ, t = 6 * n := ⟨a - b, by parley_set_side⟩
    -- 3.10. def:set-image u := t, from 3.9
    have s3_10 : t ∈ (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 6 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 6 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s3_10
  -- 4. def:subset, from 3
  have s4 : (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ) = (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) s2 s4) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) s2 s4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) s2 s4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) s2 s4) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℤ => 6 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) s2 s4); parley_set_side)
  all_goals exact s5

end Parley.Proofs.Hammack.MultiplesOfSix.MultiplesOfSix
