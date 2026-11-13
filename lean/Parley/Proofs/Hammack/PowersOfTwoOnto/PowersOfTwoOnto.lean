module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
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
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (2 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := y) (Z := Set.univ) (Set.mapsTo_univ _ _))).mp hK1
    -- 1.2. calculation
    have s1_2 : y = f m := by
      calc y = 2 ^ m := by exact s1_1
        _ = f m := by exact (hH2 m).symm
    -- 1.3. exhibit, from 1.2
    exact ⟨m, s1_2⟩
  -- 2. def:onto, from H1, 1
  exact ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℤ)) (Y := (fun n : ℤ => (2 ^ n : ℚ)) '' (Set.univ : Set ℤ)) (f := f) hH1)).mpr ⟨hH1, by simpa only [Set.mem_univ, true_and] using s1⟩

end Parley.Proofs.Hammack.PowersOfTwoOnto.PowersOfTwoOnto
