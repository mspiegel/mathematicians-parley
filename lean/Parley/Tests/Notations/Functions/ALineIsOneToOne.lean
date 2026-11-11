module

public import NormTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ALineIsOneToOne

theorem a_line_is_one_to_one (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = 2 * x + 1) :
    (Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ)) := by
  -- 1. mun:function-into
  -- 2. proof
  have s2 : ∀ s : ℝ, ∀ t : ℝ, f s = f t → s = t := by
    intro s
    intro t
    intro hA1
    -- 2.1. D1
    have s2_1 : f s = 2 * s + 1 := by simp (disch := omega) only [hD1]
    -- 2.2. D1
    have s2_2 : f t = 2 * t + 1 := by simp (disch := omega) only [hD1]
    -- 2.3. calculation
    have s2_3 : 2 * s + 1 = 2 * t + 1 := by
      calc 2 * s + 1 = f s := by exact s2_1.symm
        _ = f t := by parley_set_side
        _ = 2 * t + 1 := by exact s2_2
    -- 2.4. algebra, from 2.3
    linear_combination (norm := parley_norm) ((1 / 2 : ℝ)) * s2_3
  -- 3. def:one-to-one, from 1, 2
  exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side)

end Parley.Tests.Notations.Functions.ALineIsOneToOne
