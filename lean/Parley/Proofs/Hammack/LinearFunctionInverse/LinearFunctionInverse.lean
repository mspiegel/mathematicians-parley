module

public import AlgebraTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/hammack/linear-function-inverse.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LinearFunctionInverse.LinearFunctionInverse

theorem linear_function_inverse (x : ℝ) :
    ((Real.pi * x - Real.exp 1 + Real.exp 1) / Real.pi = x ∧ Real.pi * ((x + Real.exp 1) / Real.pi) - Real.exp 1 = x) := by
  -- 1. real arithmetic
  have s1 : 0 < Real.pi := by parley_real
  -- 2. algebra
  have r10_1 : 0 ≠ Real.pi := ne_of_lt (by linarith only [s1])
  have s2 : (Real.pi * x - Real.exp 1 + Real.exp 1) / Real.pi = x := by parley_ring
  -- 3. algebra
  have r14_1 : 0 ≠ Real.pi := ne_of_lt (by linarith only [s1])
  have s3 : Real.pi * ((x + Real.exp 1) / Real.pi) - Real.exp 1 = x := by parley_ring
  -- 4. join 2, 3
  have s4a : (Real.pi * x - Real.exp 1 + Real.exp 1) / Real.pi = x := s2
  have s4b : Real.pi * ((x + Real.exp 1) / Real.pi) - Real.exp 1 = x := s3
  exact ⟨s4a, s4b⟩

end Parley.Proofs.Hammack.LinearFunctionInverse.LinearFunctionInverse
