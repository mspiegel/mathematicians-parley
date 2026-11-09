module

public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sets

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.HalfTurn

theorem half_turn (x : ℝ) (hH2 : x ∈ ({-Real.pi, Real.pi} : Set ℝ)) :
    (∃ j : ℤ, x = (2 * (j : ℝ) + 1) * Real.pi) := by
  -- 1. def:pair u := −π, w := π, from H2
  have s1 : x = -Real.pi ∨ x = Real.pi := ((Parley.Items.Stdlib.Sets.def_pair (u := -Real.pi) (w := Real.pi) (x := x))).mp hH2
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. algebra, from C1
    have s2_1 : x = (2 * -1 + 1) * Real.pi := by linear_combination (norm := parley_norm) hC1
    -- 2.2. exhibit, from 2.1
    exact ⟨(-1 : ℤ), by exact_mod_cast s2_1⟩
  · skip
    -- 2.3. algebra, from C2
    have s2_3 : x = (2 * 0 + 1) * Real.pi := by linear_combination (norm := parley_norm) hC2
    -- 2.4. exhibit, from 2.3
    exact ⟨(0 : ℤ), by exact_mod_cast s2_3⟩

end Parley.Stdlib.Geometry.HalfTurn
