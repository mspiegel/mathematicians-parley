module

public import NormTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ALineIsOneToOneAndOnto

set_option maxHeartbeats 400000 in
theorem a_line_is_one_to_one_and_onto (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = 2 * x + 1) :
    (Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ) ∧ Set.SurjOn f (Set.univ : Set ℝ) (Set.univ : Set ℝ)) := by
  -- 1. mun:function-into
  -- 2. proof
  have s2 : ∀ s : ℝ, ∀ t : ℝ, f s = f t → s = t := by
    intro s
    intro t
    intro hA1
    -- 2.1. calculation
    have s2_1 : 2 * s + 1 = 2 * t + 1 := by
      calc 2 * s + 1 = f s := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
        _ = f t := by parley_set_side
        _ = 2 * t + 1 := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
    -- 2.2. algebra, from 2.1
    linear_combination (norm := parley_norm) ((1 / 2 : ℝ)) * s2_1
  -- 3. proof
  have s3 : ∀ y : ℝ, ∃ x : ℝ, y = f x := by
    intro y
    -- 3.1. D1
    have s3_1 : f ((y - 1) / 2) = 2 * ((y - 1) / 2) + 1 := by (try simp only [hD1]); first | done | parley_set_side
    -- 3.2. algebra, from 3.1
    have s3_2 : y = f ((y - 1) / 2) := by linear_combination (norm := parley_norm) ((-2) / ((2))) * s3_1
    -- 3.3. exhibit, from 3.2
    exact ⟨(y - 1) / 2, s3_2⟩
  -- 4. def:one-to-one, from 1, 2
  have s4 : Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 5. def:onto, from 1, 3
  have s5 : Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.SurjOn f (Set.univ : Set ℝ) (Set.univ : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 6. def:one-to-one-onto, from 4, 5
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)

end Parley.Tests.Notations.Functions.ALineIsOneToOneAndOnto
