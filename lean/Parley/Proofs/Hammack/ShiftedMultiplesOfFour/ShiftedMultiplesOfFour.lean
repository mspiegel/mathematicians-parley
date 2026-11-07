module

public import NormTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/shifted-multiples-of-four.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ShiftedMultiplesOfFour.ShiftedMultiplesOfFour

set_option maxHeartbeats 400000 in
theorem shifted_multiples_of_four :
    (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ) = (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by
  -- 1. proof
  have s1 : ∀ t ∈ (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ), t ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by
    intro t hK1
    -- 1.1. obtain m: def:set-image u := t, from K1
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 5)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 1.2. algebra, from 1.1
    have s1_2 : t = 4 * (m + 1) + 1 := by linear_combination (norm := parley_norm) s1_1
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ k : ℤ, t = 4 * k + 1 := ⟨m + 1, by parley_set_side⟩
    -- 1.4. def:set-image u := t, from 1.3
    have s1_4 : t ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_4
  -- 2. def:subset, from 1
  have s2 : (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ) ⊆ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ t ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ), t ∈ (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ) := by
    intro t hK2
    -- 3.1. obtain m: def:set-image u := t, from K2
    obtain ⟨m, _, s3_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 3.2. algebra, from 3.1
    have s3_2 : t = 4 * (m - 1) + 5 := by linear_combination (norm := parley_norm) s3_1
    -- 3.3. exhibit, from 3.2
    have s3_3 : ∃ k : ℤ, t = 4 * k + 5 := ⟨m - 1, by parley_set_side⟩
    -- 3.4. def:set-image u := t, from 3.3
    have s3_4 : t ∈ (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 5)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 5)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s3_4
  -- 4. def:subset, from 3
  have s4 : (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) ⊆ (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ) = (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun k : ℤ => 4 * k + 5) '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) s2 s4)
  all_goals exact s5

end Parley.Proofs.Hammack.ShiftedMultiplesOfFour.ShiftedMultiplesOfFour
