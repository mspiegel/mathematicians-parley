module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/cases-by-implication.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.CasesByImplication.CasesByImplication

theorem cases_by_implication (a : ℝ) (b : ℝ) (c : ℝ) :
    ((a = 0 → c = 0) → (b = 0 → c = 0) → a = 0 ∨ b = 0 → c = 0) := by
  -- the theorem. proof
  have sThm : (a = 0 → c = 0) → (b = 0 → c = 0) → a = 0 ∨ b = 0 → c = 0 := by
    intro hK1
    intro hK2
    intro hK3
    -- 1. cases, from K3
    have s1 : c = 0 := by
      rcases hK3 with hC1 | hC2
      · skip
        -- 1.1. mun:modus-ponens, from C1, K1
        have s1_1 : c = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1)
        all_goals parley_side
      · skip
        -- 1.2. mun:modus-ponens, from C2, K2
        have s1_2 : c = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2)
        all_goals parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.CasesByImplication.CasesByImplication
