module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ALineIsOnto

theorem a_line_is_onto (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = 2 * x + 1) :
    (Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.SurjOn f (Set.univ : Set ℝ) (Set.univ : Set ℝ)) := by
  -- 1. mun:function-into
  -- 2. proof
  have s2 : ∀ y : ℝ, ∃ x : ℝ, y = f x := by
    intro y
    -- 2.1. D1
    have s2_1 : f ((y - 1) / 2) = 2 * ((y - 1) / 2) + 1 := by (try simp only [hD1]); first | done | parley_set_side
    -- 2.2. algebra, from 2.1
    have s2_2 : y = f ((y - 1) / 2) := by linear_combination (norm := parley_norm) ((-2) / ((2))) * s2_1
    -- 2.3. exhibit, from 2.2
    have s2_3 : ∃ x : ℝ, y = f x := ⟨(y - 1) / 2, by parley_set_side⟩
    all_goals exact s2_3
  -- 3. def:onto, from 1, 2
  have s3 : Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.SurjOn f (Set.univ : Set ℝ) (Set.univ : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s3

end Parley.Tests.Notations.Functions.ALineIsOnto
