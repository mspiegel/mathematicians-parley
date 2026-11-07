module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-exhibit-from-an-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitFromAnAnd.CosineIsNotOneToOne

theorem cosine_is_not_one_to_one :
    (∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ Real.cos x = Real.cos y) := by
  -- 1. real arithmetic
  have s1 : Real.cos (0 : ℝ) = Real.cos (2 * Real.pi) := by parley_real
  -- 2. real arithmetic
  have s2 : 0 < 2 * Real.pi := by parley_real
  -- 3. inequalities
  have s3 : 0 ≠ 2 * Real.pi := by parley_side
  -- 4. exhibit, from 1, 3
  have s4 : ∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ Real.cos x = Real.cos y := ⟨(0 : ℝ), 2 * Real.pi, ⟨by parley_side, by parley_side⟩⟩
  all_goals exact s4

end Parley.Tests.Elaborator.AnExhibitFromAnAnd.CosineIsNotOneToOne
