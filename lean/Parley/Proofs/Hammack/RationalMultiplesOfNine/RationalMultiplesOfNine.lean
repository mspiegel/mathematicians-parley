module

public import NormTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Init
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

/-! Written from proofs/hammack/rational-multiples-of-nine.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalMultiplesOfNine.RationalMultiplesOfNine

set_option maxHeartbeats 400000 in
theorem rational_multiples_of_nine :
    (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) = (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by
  -- 1. proof
  have s1 : ∀ t ∈ (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ), t ∈ (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by
    intro t hK1
    -- 1.1. obtain m: def:set-image u := t, from K1
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 9 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 1.2. algebra, from 1.1
    have s1_2 : t = 3 * (3 * m) := by linear_combination (norm := parley_norm) s1_1
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ n : ℚ, t = 3 * n := ⟨3 * m, s1_2⟩
    -- 1.4. def:set-image u := t, from 1.3
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 3 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 3 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 2. def:subset, from 1
  have s2 : (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) ⊆ (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)))).mpr s1; parley_set_side)
  -- 3. proof
  have s3 : ∀ t ∈ (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ), t ∈ (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) := by
    intro t hK2
    -- 3.1. obtain m: def:set-image u := t, from K2
    obtain ⟨m, _, s3_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 3 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 3.2. algebra, from 3.1
    have s3_2 : t = 9 * (m / 3) := by linear_combination (norm := parley_norm) ((3) / ((3))) * s3_1
    -- 3.3. exhibit, from 3.2
    have s3_3 : ∃ n : ℚ, t = 9 * n := ⟨m / 3, s3_2⟩
    -- 3.4. def:set-image u := t, from 3.3
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 9 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 9 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 4. def:subset, from 3
  have s4 : (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) ⊆ (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)))).mpr s3 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)))).mpr s3; parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) s2 s4)

end Parley.Proofs.Hammack.RationalMultiplesOfNine.RationalMultiplesOfNine
