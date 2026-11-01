module

public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from proofs/setmm/contrapositive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Contrapositive.Contrapositive

theorem contrapositive (a : ℝ) (b : ℝ) :
    ((a = 0 → b = 0) → b ≠ 0 → a ≠ 0) := by
  -- the theorem. proof
  have sThm : (a = 0 → b = 0) → b ≠ 0 → a ≠ 0 := by
    intro hK1
    intro hK2
    by_contra hc_hS
    have hS : a = 0 := by parley_suppose hc_hS
    -- 1. mun:modus-ponens, from K1, S
    have s1 : b = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side))).symm
    -- 2. restate K2
    have s2 : b ≠ 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.Contrapositive.Contrapositive
