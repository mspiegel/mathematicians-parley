module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/implication-and-currying.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImplicationAndCurrying.ImplicationAndCurrying

theorem implication_and_currying (a : ℝ) (b : ℝ) (c : ℝ) :
    (a = 0 ∧ b = 0 → c = 0 ↔ a = 0 → b = 0 → c = 0) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    intro hK1
    intro hK2
    -- 1. join K1, K2
    have s1 : a = 0 ∧ b = 0 := ⟨hK1, hK2⟩
    -- 2. mun:modus-ponens, from D1, 1
    exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 s1)
  · skip
    intro hD2
    intro hK3
    -- 3. mun:modus-ponens, from D2, K3
    have s3 : b = 0 → c = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) hD2 hK3.1)
    -- 4. mun:modus-ponens, from K3, 3
    exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2)

end Parley.Proofs.Setmm.ImplicationAndCurrying.ImplicationAndCurrying
