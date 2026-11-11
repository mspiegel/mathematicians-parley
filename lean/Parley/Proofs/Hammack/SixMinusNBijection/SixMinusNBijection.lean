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
public import Mathlib.Tactic.Positivity.Basic
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
      calc 6 - s = f s := by exact (hH2 s).symm
        _ = f t := by parley_set_side
        _ = 6 - t := by exact (hH2 t)
    -- 1.2. algebra, from 1.1
    linear_combination (norm := parley_norm) (-1) * s1_1
  -- 2. def:one-to-one, from H1, 1
  have s2 : Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.InjOn f (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr ⟨by parley_set_side, by parley_set_side⟩
  -- 3. proof
  have s3 : ∀ y : ℤ, ∃ x : ℤ, y = f x := by
    intro y
    -- 3.1. instantiate n := 6 − y in H2
    have s3_1 : f (6 - y) = 6 - (6 - y) := by exact (hH2 (6 - y))
    -- 3.2. algebra, from 3.1
    have s3_2 : y = f (6 - y) := by linear_combination (norm := parley_norm) (-1) * s3_1
    -- 3.3. exhibit, from 3.2
    exact ⟨6 - y, s3_2⟩
  -- 4. def:onto, from H1, 3
  have s4 : Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.SurjOn f (Set.univ : Set ℤ) (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr ⟨by parley_set_side, by parley_set_side⟩
  -- 5. def:one-to-one-onto, from 2, 4
  exact ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side)

end Parley.Proofs.Hammack.SixMinusNBijection.SixMinusNBijection
