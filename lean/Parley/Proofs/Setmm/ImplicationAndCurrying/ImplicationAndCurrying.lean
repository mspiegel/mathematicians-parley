module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/implication-and-currying.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImplicationAndCurrying.ImplicationAndCurrying

theorem implication_and_currying (a : ℝ) (b : ℝ) (c : ℝ) :
    (a = 0 ∧ b = 0 → c = 0 ↔ a = 0 → b = 0 → c = 0) := by
  -- the theorem. both directions
  have sThm : a = 0 ∧ b = 0 → c = 0 ↔ a = 0 → b = 0 → c = 0 := by
    constructor
    · skip
      intro hD1
      intro hK1
      intro hK2
      -- 1. join K1, K2
      have s1 : a = 0 ∧ b = 0 := by parley_side
      -- 2. mun:modus-ponens, from D1, 1
      have s2 : c = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) hD1 (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      intro hK3
      -- 3. mun:modus-ponens, from D2, K3
      have s3 : b = 0 → c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) hD2 hK3.1) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) hD2 hK3.1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) hD2 hK3.1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) hD2 hK3.1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) hD2 hK3.1); parley_side)
      -- 4. mun:modus-ponens, from K3, 3
      have s4 : c = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) s3 hK3.2); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.ImplicationAndCurrying.ImplicationAndCurrying
