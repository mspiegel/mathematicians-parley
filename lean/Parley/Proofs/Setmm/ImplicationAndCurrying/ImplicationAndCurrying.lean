module

public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

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
      have s2 : c = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 ∧ b = 0) (Q := c = 0) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
      all_goals parley_side
    · skip
      intro hD2
      intro hK3
      -- 3. mun:modus-ponens, from D2, K3
      have s3 : b = 0 → c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side))
      -- 4. mun:modus-ponens, from K3, 3
      have s4 : c = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := b = 0) (Q := c = 0) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.ImplicationAndCurrying.ImplicationAndCurrying
