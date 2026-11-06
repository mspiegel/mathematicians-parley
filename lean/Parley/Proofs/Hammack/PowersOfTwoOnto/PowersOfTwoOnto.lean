module

public import PowerTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/hammack/powers-of-two-onto.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PowersOfTwoOnto.PowersOfTwoOnto

theorem powers_of_two_onto (f : ℤ → ℚ) (hH1 : Set.MapsTo f (Set.univ : Set ℤ) ((fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ))) (hH2 : ∀ n : ℤ, f n = 2 ^ n) :
    (Set.MapsTo f (Set.univ : Set ℤ) ((fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ)) ∧ Set.SurjOn f (Set.univ : Set ℤ) ((fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ))) := by
  -- 1. proof
  have s1 : ∀ y ∈ (fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ), ∃ x : ℤ, y = f x := by
    intro y hK1
    -- 1.1. obtain m: def:set-image u := y, from K1
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (2 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := y) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 1.2. calculation
    have s1_2 : y = f m := by
      calc y = 2 ^ m := by parley_set_side
        _ = f m := by first | linear_combination (norm := parley_norm) (hH2 m) | (have h := (hH2 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 m) | exact_mod_cast ((hH2 m)).symm | (have h := (hH2 m); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 m); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 m); parley_int_power h) | (have h := (hH2 m); parley_set_side)
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ x : ℤ, y = f x := ⟨m, by parley_set_side⟩
    all_goals exact s1_3
  -- 2. def:onto, from H1, 1
  have s2 : Set.MapsTo f (Set.univ : Set ℤ) ((fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ)) ∧ Set.SurjOn f (Set.univ : Set ℤ) ((fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℤ)) (Y := (fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℤ)) (Y := (fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.PowersOfTwoOnto.PowersOfTwoOnto
