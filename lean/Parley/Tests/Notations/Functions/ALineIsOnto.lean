module

public import NormTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
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
    exact ⟨(y - 1) / 2, s2_2⟩
  -- 3. def:onto, from 1, 2
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)

end Parley.Tests.Notations.Functions.ALineIsOnto
