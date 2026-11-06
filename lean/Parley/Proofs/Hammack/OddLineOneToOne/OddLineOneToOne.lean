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

/-! Written from proofs/hammack/odd-line-one-to-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddLineOneToOne.OddLineOneToOne

theorem odd_line_one_to_one (f : ℤ → ℤ) (hH2 : ∀ n : ℤ, f n = 2 * n + 1) :
    (Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.InjOn f (Set.univ : Set ℤ)) := by
  -- 1. proof
  have s1 : ∀ s : ℤ, ∀ t : ℤ, f s = f t → s = t := by
    intro s
    intro t
    intro hA1
    -- 1.1. calculation
    have s1_1 : 2 * s + 1 = 2 * t + 1 := by
      calc 2 * s + 1 = f s := by first | linear_combination (norm := parley_norm) (hH2 s) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 s) | exact_mod_cast ((hH2 s)).symm | (have h := (hH2 s); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); parley_int_power h) | (have h := (hH2 s); parley_set_side)
        _ = f t := by parley_set_side
        _ = 2 * t + 1 := by first | linear_combination (norm := parley_norm) (hH2 t) | (have h := (hH2 t); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 t); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 t) | exact_mod_cast ((hH2 t)).symm | (have h := (hH2 t); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 t); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 t); parley_int_power h) | (have h := (hH2 t); parley_set_side)
    -- 1.2. algebra, from 1.1
    have s1_2 : s = t := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s1_1
    all_goals parley_set_side
  -- 2. def:one-to-one, from H1, 1
  have s2 : Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.InjOn f (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.OddLineOneToOne.OddLineOneToOne
