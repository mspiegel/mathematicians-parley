module

public import ArithTactics
public import NormTactics
public import PowerTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Reasoning

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
    have s1 : b = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0) hK1 hS); parley_side)
    -- 2. restate K2
    have s2 : b ≠ 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.Contrapositive.Contrapositive
