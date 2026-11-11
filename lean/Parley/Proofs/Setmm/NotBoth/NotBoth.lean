module

public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/not-both.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NotBoth.NotBoth

theorem not_both (a : ℝ) (b : ℝ) :
    (¬ (a = 0 ∧ b = 0) ↔ a ≠ 0 ∨ b ≠ 0) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    by_contra hS
    -- 1. mun:not-either, from S
    have s1a : ¬ a ≠ 0 := by exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp hS).1
    have s1b : ¬ b ≠ 0 := by exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp hS).2
    -- 2. mun:double-negation, from 1
    have s2 : a = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a)
    -- 3. mun:double-negation, from 1
    have s3 : b = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b)
    -- 4. join 2, 3
    have s4 : a = 0 ∧ b = 0 := by parley_side
    exact hD1 s4
  · skip
    intro hD2
    -- 5. cases, from D2
    rcases hD2 with hC1 | hC2
    · skip
      intro hS1
      -- 5.1. restate C1
      have s5_1 : a ≠ 0 := by exact hC1
      exact s5_1 hS1.1
    · skip
      intro hS2
      -- 5.2. restate C2
      have s5_2 : b ≠ 0 := by exact hC2
      exact s5_2 hS2.2

end Parley.Proofs.Setmm.NotBoth.NotBoth
