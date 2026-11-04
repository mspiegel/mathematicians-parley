module

public import PowerTactics
public import Tactics
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
        have s1_1 : c = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := c = 0) hK1 hC1); parley_side)
        all_goals parley_side
      · skip
        -- 1.2. mun:modus-ponens, from C2, K2
        have s1_2 : c = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) hK2 hC2); parley_side)
        all_goals parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.CasesByImplication.CasesByImplication
