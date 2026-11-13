module

public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/multiples-of-twelve.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MultiplesOfTwelve.MultiplesOfTwelve

theorem multiples_of_twelve :
    (fun n : ℤ => 12 * n) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by
  -- 1. proof
  have s1 : ∀ t ∈ (fun n : ℤ => 12 * n) '' (Set.univ : Set ℤ), t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by
    intro t hK1
    -- 1.1. obtain m: def:set-image u := t, from K1
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 12 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (Set.mapsTo_univ _ _))).mp hK1
    -- 1.2. algebra, from 1.1
    have s1_2 : t = 2 * (6 * m) := by linear_combination (norm := parley_norm) s1_1
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ n : ℤ, t = 2 * n := ⟨6 * m, s1_2⟩
    -- 1.4. def:set-image u := t, from 1.3
    have s1_4 : t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (Set.mapsTo_univ _ _))).mpr (by simpa only [Set.mem_univ, true_and] using s1_3)
    -- 1.5. algebra, from 1.1
    have s1_5 : t = 3 * (4 * m) := by linear_combination (norm := parley_norm) s1_1
    -- 1.6. exhibit, from 1.5
    have s1_6 : ∃ n : ℤ, t = 3 * n := ⟨4 * m, s1_5⟩
    -- 1.7. def:set-image u := t, from 1.6
    have s1_7 : t ∈ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 3 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (Set.mapsTo_univ _ _))).mpr (by simpa only [Set.mem_univ, true_and] using s1_6)
    -- 1.8. def:intersection u := t, from 1.4, 1.7
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mpr ⟨s1_4, s1_7⟩
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => 12 * n) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)))).mpr s1

end Parley.Proofs.Hammack.MultiplesOfTwelve.MultiplesOfTwelve
