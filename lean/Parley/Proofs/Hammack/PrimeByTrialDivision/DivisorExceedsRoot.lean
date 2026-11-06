module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/prime-by-trial-division.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot

theorem divisor_exceeds_root (p : ℤ) (hH1 : 0 < p) (d : ℤ) (hH2 : 0 < d) (hH3 : 2 ≤ d) (hH4 : d ∣ p) (hH5 : ∀ n : ℤ, 0 < n → 2 ≤ n ∧ (n : ℝ) ≤ Real.sqrt (p : ℝ) → ¬ n ∣ p) :
    p < d * d := by
  -- 1. def:sqrt x := p
  have r22_1 : p ≥ 0 := by parley_order
  have s1a : Real.sqrt (p : ℝ) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (p : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (p : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (p : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (p : ℝ)) (by parley_side)); parley_side)
  have s1b : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side)); parley_side)
  -- 2. contradiction
  have s2 : p < d * d := by
    by_contra hc_hS
    have hS : ¬ p < d * d := by parley_suppose hc_hS
    -- 2.1. inequalities, from S
    have s2_1 : d * d ≤ p := by parley_order
    -- 2.2. calculation
    have s2_2 : (d : ℝ) ^ 2 ≤ Real.sqrt (p : ℝ) ^ 2 := by
      calc (d : ℝ) ^ 2 = (d : ℝ) * (d : ℝ) := by parley_ring
        _ ≤ (p : ℝ) := by parley_side
        _ = Real.sqrt (p : ℝ) ^ 2 := by parley_side
    -- 2.3. mun:square-le x := d, y := √p, from 1, 2.2
    have r39_1 : d ≥ 0 := by parley_order
    have s2_3 : (d : ℝ) ≤ Real.sqrt (p : ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (d : ℝ)) (y := Real.sqrt (p : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (d : ℝ)) (y := Real.sqrt (p : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
    -- 2.4. join H3, 2.3
    have s2_4a : 2 ≤ d := by parley_side
    have s2_4b : (d : ℝ) ≤ Real.sqrt (p : ℝ) := by parley_side
    -- 2.5. instantiate n := d in H5, from H2
    have s2_5 : 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ) → ¬ d ∣ p := by first | exact (hH5 d (by parley_side)) | exact ((hH5 d (by parley_side))).symm | simpa using (hH5 d (by parley_side)) | exact_mod_cast (hH5 d (by parley_side)) | (have h := (hH5 d (by parley_side)); parley_side)
    -- 2.6. mun:modus-ponens P := 2 ≤ d and d ≤ √p, from 2.4, 2.5
    have s2_6 : ¬ d ∣ p := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ)) (Q := ¬ d ∣ p) s2_5 (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ)) (Q := ¬ d ∣ p) s2_5 (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ)) (Q := ¬ d ∣ p) s2_5 (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ)) (Q := ¬ d ∣ p) s2_5 (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ)) (Q := ¬ d ∣ p) s2_5 (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ)) (Q := ¬ d ∣ p) s2_5 (by parley_side)); parley_side)
    all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot
