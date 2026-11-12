module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/hammack/cosine-is-not-injective.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CosineIsNotInjective.CosineIsNotInjective

theorem cosine_is_not_injective :
    (∃ x : ℝ, ∃ y : ℝ, x ≠ y ∧ Real.cos x = Real.cos y) := by
  -- 1. real arithmetic
  have s1 : Real.cos (0 : ℝ) = Real.cos (2 * Real.pi) := by parley_real
  -- 2. real arithmetic
  have s2 : 0 < 2 * Real.pi := by parley_real
  -- 3. inequalities
  have s3 : 0 ≠ 2 * Real.pi := ne_of_lt (by linarith only [s2])
  -- 4. join 1, 3
  have s4a : 0 ≠ 2 * Real.pi := by parley_side
  have s4b : Real.cos (0 : ℝ) = Real.cos (2 * Real.pi) := by parley_side
  -- 5. exhibit, from 4
  exact ⟨(0 : ℝ), 2 * Real.pi, ⟨s4a, s4b⟩⟩

end Parley.Proofs.Hammack.CosineIsNotInjective.CosineIsNotInjective
