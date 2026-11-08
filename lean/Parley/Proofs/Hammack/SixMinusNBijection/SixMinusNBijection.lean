module

public import NormTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/hammack/six-minus-n-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SixMinusNBijection.SixMinusNBijection

theorem six_minus_n_bijection (f : ℤ → ℤ) (hH2 : ∀ n : ℤ, f n = 6 - n) :
    (Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.InjOn f (Set.univ : Set ℤ) ∧ Set.SurjOn f (Set.univ : Set ℤ) (Set.univ : Set ℤ)) := by
  -- 1. proof
  have s1 : ∀ s : ℤ, ∀ t : ℤ, f s = f t → s = t := by
    intro s
    intro t
    intro hA1
    -- 1.1. calculation
    have s1_1 : 6 - s = 6 - t := by
      calc 6 - s = f s := by first | linear_combination (norm := parley_norm) (hH2 s) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 s) | exact_mod_cast ((hH2 s)).symm | (have h := (hH2 s); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); parley_int_power h) | (have h := (hH2 s); parley_set_side)
        _ = f t := by parley_set_side
        _ = 6 - t := by first | linear_combination (norm := parley_norm) (hH2 t) | (have h := (hH2 t); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 t); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 t) | exact_mod_cast ((hH2 t)).symm | (have h := (hH2 t); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 t); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 t); parley_int_power h) | (have h := (hH2 t); parley_set_side)
    -- 1.2. algebra, from 1.1
    linear_combination (norm := parley_norm) (-1) * s1_1
  -- 2. def:one-to-one, from H1, 1
  have s2 : Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.InjOn f (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ y : ℤ, ∃ x : ℤ, y = f x := by
    intro y
    -- 3.1. instantiate n := 6 − y in H2
    have s3_1 : f (6 - y) = 6 - (6 - y) := by first | linear_combination (norm := parley_norm) (hH2 (6 - y)) | (have h := (hH2 (6 - y)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (6 - y)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (6 - y)) | exact_mod_cast ((hH2 (6 - y))).symm | (have h := (hH2 (6 - y)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (6 - y)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (6 - y)); parley_int_power h) | (have h := (hH2 (6 - y)); parley_set_side)
    -- 3.2. algebra, from 3.1
    have s3_2 : y = f (6 - y) := by linear_combination (norm := parley_norm) (-1) * s3_1
    -- 3.3. exhibit, from 3.2
    exact ⟨6 - y, s3_2⟩
  -- 4. def:onto, from H1, 3
  have s4 : Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.SurjOn f (Set.univ : Set ℤ) (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 5. def:one-to-one-onto, from 2, 4
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)

end Parley.Proofs.Hammack.SixMinusNBijection.SixMinusNBijection
