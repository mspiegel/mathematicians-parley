module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from proofs/setmm/no-least-positive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NoLeastPositive.NoLeastPositive

theorem no_least_positive :
    ¬ (∃ x : ℝ, 0 < x ∧ ¬ (∃ y : ℝ, 0 < y ∧ y < x)) := by
  -- 1. contradiction
  intro hS
  -- 1.1. obtain x from S
  obtain ⟨x, ⟨s1_1a, s1_1b⟩⟩ := hS
  -- 1.2. inequalities
  have s1_2 : 0 < x / 2 := by linarith only [s1_1a]
  -- 1.3. inequalities
  have s1_3 : x / 2 < x := by linarith only [s1_2]
  -- 1.4. exhibit, from 1.2, 1.3
  have s1_4 : ∃ y : ℝ, 0 < y ∧ y < x := ⟨x / 2, ⟨s1_2, s1_3⟩⟩
  exact s1_1b s1_4

end Parley.Proofs.Setmm.NoLeastPositive.NoLeastPositive
