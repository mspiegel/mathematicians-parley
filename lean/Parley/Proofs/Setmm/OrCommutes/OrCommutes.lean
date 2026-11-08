module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/or-commutes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OrCommutes.OrCommutes

theorem or_commutes (a : ℝ) (b : ℝ) :
    (a = 0 ∨ b = 0 ↔ b = 0 ∨ a = 0) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. cases, from D1
    rcases hD1 with hC1 | hC2
    · skip
      -- 1.1. mun:or-right, from C1
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := a = 0) hC1)
    · skip
      -- 1.2. mun:or-left, from C2
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b = 0) (Q := a = 0) hC2)
  · skip
    intro hD2
    -- 2. cases, from D2
    rcases hD2 with hC3 | hC4
    · skip
      -- 2.1. mun:or-right, from C3
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) hC3)
    · skip
      -- 2.2. mun:or-left, from C4
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) hC4)

end Parley.Proofs.Setmm.OrCommutes.OrCommutes
