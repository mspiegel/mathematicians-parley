module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/one-minus-half-power-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OneMinusHalfPowerLimit.OneMinusHalfPowerLimit

set_option maxHeartbeats 600000 in
theorem one_minus_half_power_limit (a : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → a n = 1 - 1 / 2 ^ n.toNat) :
    Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds 1) := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → k ≤ 2 ^ k.toNat := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) ≤ 2 ^ 1 := by parley_arith
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. mun:exponent-step a := 2, m := k
      have s1_2 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side)); parley_side)
      -- 1.3. inequalities, from K
      have s1_3 : k + 1 ≤ 2 * k := by parley_order
      -- 1.4. inequalities
      have s1_4 : 2 * k ≤ 2 * 2 ^ k.toNat := by parley_order
      -- 1.5. algebra
      have s1_5 : (2 * 2 ^ k.toNat : ℤ) = 2 ^ k.toNat * 2 := by parley_ring
      -- 1.6. transitivity, from 1.3, 1.4, 1.5, 1.2
      have s1_6 : k + 1 ≤ 2 ^ (k + 1).toNat := by parley_order
      all_goals parley_side
  -- 2. proof
  have s2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 1) < ε)) := by
    intro ε
    intro hA1
    -- 2.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s2_1a, s2_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) (by parley_side))
    -- 2.2. proof
    have s2_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 1) < ε := by
      intro n hK2
      intro hA2
      -- 2.2.1. inequalities, from K2
      have s2_2_1 : n > 0 := by parley_order
      -- 2.2.2. mun:power-positive a := 2, m := n
      have r63_1 : (2 : ℤ) > 0 := by parley_arith
      have s2_2_2 : (2 ^ n.toNat : ℤ) > 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)); parley_side)
      -- 2.2.3. mun:reciprocal-order x := n, y := 2^n, from 1
      have r67_1 : n > 0 := by parley_side
      have r67_2 : (2 ^ n.toNat : ℤ) > 0 := by parley_side
      have s2_2_3 : 1 / 2 ^ n.toNat ≤ 1 / (n : ℚ) := by first | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℚ)) (by parley_side) (y := (2 ^ n.toNat : ℚ)) (by parley_side))).mp (by parley_side); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℚ)) (by parley_side) (y := (2 ^ n.toNat : ℚ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℚ)) (by parley_side) (y := (2 ^ n.toNat : ℚ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℚ)) (by parley_side) (y := (2 ^ n.toNat : ℚ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℚ)) (by parley_side) (y := (2 ^ n.toNat : ℚ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 2.2.4. mun:reciprocal-order x := N, y := n, from A2
      have r72_1 : N > 0 := by parley_order
      have r72_2 : n > 0 := by parley_side
      have s2_2_4 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 2.2.5. transitivity, from 2.2.3, 2.2.4, 2.1
      have s2_2_5 : 1 / 2 ^ n.toNat < ε := by parley_order
      -- 2.2.6. inequalities
      have s2_2_6 : 1 - ε < 1 - 1 / 2 ^ n.toNat := by parley_order
      -- 2.2.7. transitivity, from 2.2.6, H2
      have s2_2_7 : 1 - ε < a n := by have := (hH2 n (by parley_side)); parley_order
      -- 2.2.8. mun:reciprocal-positive x := 2^n, from 2.2.2
      have s2_2_8 : (1 / 2 ^ n.toNat : ℚ) > 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)); parley_side)
      -- 2.2.9. inequalities
      have s2_2_9 : (1 - 1 / 2 ^ n.toNat : ℚ) < 1 := by parley_order
      -- 2.2.10. inequalities
      have s2_2_10 : 1 < 1 + ε := by parley_order
      -- 2.2.11. transitivity, from H2, 2.2.9, 2.2.10
      have s2_2_11 : a n < 1 + ε := by have := (hH2 n (by parley_side)); parley_order
      -- 2.2.12. join 2.2.7, 2.2.11
      have s2_2_12 : 1 - ε < a n ∧ a n < 1 + ε := by parley_side
      -- 2.2.13. mun:abs-difference-lt x := a(n), c := 1, δ := ε, from 2.2.12
      have s2_2_13 : abs (a n - 1) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := (1 : ℝ)) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := (1 : ℝ)) (δ := ε))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 2.3. exhibit, from 2.2
    have s2_3 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 1) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 3. def:tends-to L := 1, from 2
  have s3 : Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (1 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (1 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.OneMinusHalfPowerLimit.OneMinusHalfPowerLimit
