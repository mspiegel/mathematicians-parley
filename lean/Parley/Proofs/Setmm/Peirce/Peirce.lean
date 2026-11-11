module

public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/peirce.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Peirce.Peirce

theorem peirce (a : ℝ) (b : ℝ) :
    (((a = 0 → b = 0) → a = 0) → a = 0) := by
  -- the theorem. proof
  intro hK1
  by_contra (hS : a ≠ 0)
  -- 1. proof
  have s1 : a = 0 → b = 0 := by
    intro hK2
    -- 1.1. restate S
    have s1_1 : a ≠ 0 := by exact hS
    exact absurd hK2 s1_1
  -- 2. mun:modus-ponens, from K1, 1
  have s2 : a = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 → b = 0) (Q := a = 0) hK1 s1)
  exact hS s2

end Parley.Proofs.Setmm.Peirce.Peirce
