module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/not-either.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NotEither.NotEither

theorem not_either (a : ℝ) (b : ℝ) :
    (¬ (a = 0 ∨ b = 0) ↔ a ≠ 0 ∧ b ≠ 0) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. contradiction
    have s1 : a ≠ 0 := by
      intro hS1
      -- 1.1. mun:or-left, from S1
      have s1_1 : a = 0 ∨ b = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) hS1)
      -- 1.2. restate D1
      have s1_2 : ¬ (a = 0 ∨ b = 0) := by parley_side
      exact s1_2 s1_1
    -- 2. contradiction
    have s2 : b ≠ 0 := by
      intro hS2
      -- 2.1. mun:or-right, from S2
      have s2_1 : a = 0 ∨ b = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) hS2)
      -- 2.2. restate D1
      have s2_2 : ¬ (a = 0 ∨ b = 0) := by parley_side
      exact s2_2 s2_1
    -- 3. join 1, 2
    parley_side
  · skip
    intro hD2
    intro hS3
    -- 4. mun:disjunctive-syllogism, from D2, S3
    have s4 : a = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) hS3 hD2.2)
    -- 5. restate D2
    have s5 : a ≠ 0 := by parley_side
    exact s5 s4

end Parley.Proofs.Setmm.NotEither.NotEither
