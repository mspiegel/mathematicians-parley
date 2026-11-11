module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/contrapositive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Contrapositive.Contrapositive

theorem contrapositive (a : ℝ) (b : ℝ) :
    ((a = 0 → b = 0) → b ≠ 0 → a ≠ 0) := by
  -- the theorem. proof
  intro hK1
  intro hK2
  intro hS
  -- 1. mun:modus-ponens, from K1, S
  have s1 : b = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS)
  -- 2. restate K2
  have s2 : b ≠ 0 := by exact hK2
  exact s2 s1

end Parley.Proofs.Setmm.Contrapositive.Contrapositive
