module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/one-minus-half-power-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OneMinusHalfPowerLimit.OneMinusHalfPowerLimit

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
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_1
    | succ k hK hIH =>
      -- 1.2. mun:exponent-step a := 2, m := k
      have s1_2 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (le_of_lt (lt_of_lt_of_le zero_lt_one hK)))
      -- 1.3. inequalities, from K
      have s1_3 : k + 1 ≤ 2 * k := by linarith only [lt_of_lt_of_le zero_lt_one hK]
      -- 1.4. inequalities
      have s1_4 : 2 * k ≤ 2 * 2 ^ k.toNat := by linarith only [hIH]
      -- 1.5. algebra
      have s1_5 : (2 * 2 ^ k.toNat : ℤ) = 2 ^ k.toNat * 2 := by parley_ring
      -- 1.6. transitivity, from 1.3, 1.4, 1.5, 1.2
      exact LE.le.trans_eq (LE.le.trans_eq (le_trans s1_3 s1_4) s1_5) s1_2.symm
  -- 2. proof
  have s2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 1) < ε)) := by
    intro ε
    intro hA1
    -- 2.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s2_1a, s2_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) hA1)
    -- 2.2. proof
    have s2_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 1) < ε := by
      intro n hK2
      intro hA2
      -- 2.2.1. inequalities, from K2
      have s2_2_1 : n > 0 := by linarith only [hK2]
      -- 2.2.2. mun:power-positive a := 2, m := n
      have r63_1 : (2 : ℤ) > 0 := by parley_arith
      have s2_2_2 : (2 ^ n.toNat : ℤ) > 0 := by (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)); simp only [parley_zpow_toNat (n := n) (h := le_of_lt (lt_of_le_of_lt (by norm_num) s2_2_1))] at h ⊢; exact_mod_cast h)
      -- 2.2.3. mun:reciprocal-order x := n, y := 2^n, from 1
      have r67_1 : n > 0 := by parley_side
      have r67_2 : (2 ^ n.toNat : ℤ) > 0 := by parley_side
      have s2_2_3 : 1 / 2 ^ n.toNat ≤ 1 / (n : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r67_1) (y := (2 ^ n.toNat : ℚ)) (by exact_mod_cast gt_iff_lt.mp r67_2))).mp (by parley_side)
      -- 2.2.4. mun:reciprocal-order x := N, y := n, from A2
      have r72_1 : N > 0 := by linarith only [s2_1a]
      have r72_2 : n > 0 := by parley_side
      have s2_2_4 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r72_1) (y := (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r72_2))).mp (by parley_side)
      -- 2.2.5. transitivity, from 2.2.3, 2.2.4, 2.1
      have s2_2_5 : 1 / 2 ^ n.toNat < ε := by parley_order
      -- 2.2.6. inequalities
      have s2_2_6 : 1 - ε < 1 - 1 / 2 ^ n.toNat := by linarith only [s2_2_5]
      -- 2.2.7. transitivity, from 2.2.6, H2
      have s2_2_7 : 1 - ε < a n := by exact LT.lt.trans_eq s2_2_6 (hH2 n hK2).symm
      -- 2.2.8. mun:reciprocal-positive x := 2^n, from 2.2.2
      have s2_2_8 : (1 / 2 ^ n.toNat : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by exact_mod_cast gt_iff_lt.mp s2_2_2))
      -- 2.2.9. inequalities
      have s2_2_9 : (1 - 1 / 2 ^ n.toNat : ℚ) < 1 := by linarith only [s2_2_8]
      -- 2.2.10. inequalities
      have s2_2_10 : 1 < 1 + ε := by linarith only [hA1]
      -- 2.2.11. transitivity, from H2, 2.2.9, 2.2.10
      have s2_2_11 : a n < 1 + ε := by have := (hH2 n hK2); parley_order
      -- 2.2.12. join 2.2.7, 2.2.11
      have s2_2_12 : 1 - ε < a n ∧ a n < 1 + ε := by parley_side
      -- 2.2.13. mun:abs-difference-lt x := a(n), c := 1, δ := ε, from 2.2.12
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := (1 : ℝ)) (δ := ε))).mpr ⟨s2_2_12.1, s2_2_12.2⟩
    -- 2.3. exhibit, from 2.2
    exact ⟨N, s2_1a, s2_2⟩
  -- 3. def:tends-to L := 1, from 2
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (1 : ℝ)))).mpr s2

end Parley.Proofs.Hammack.OneMinusHalfPowerLimit.OneMinusHalfPowerLimit
