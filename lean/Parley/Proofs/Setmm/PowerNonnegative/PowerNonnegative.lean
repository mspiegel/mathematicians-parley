module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/power-nonnegative.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerNonnegative.PowerNonnegative

set_option maxHeartbeats 400000 in
theorem power_nonnegative (a : ℝ) (n : ℤ) (hH2 : 0 ≤ n) (hH3 : 0 ≤ a) :
    0 ≤ a ^ n.toNat := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → 0 ≤ a ^ m.toNat := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. algebra
      have s1_1 : a ^ 0 = 1 := by parley_ring
      -- 1.2. arithmetic
      have s1_2 : (0 : ℤ) ≤ 1 := by parley_arith
      -- 1.3. transitivity, from 1.2, 1.1
      have s1_3 : 0 ≤ a ^ 0 := by parley_order
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.4. mun:exponent-step
      have s1_4 : a ^ (m + 1).toNat = a ^ m.toNat * a := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m) (by parley_side))
      -- 1.5. axi:trichotomy x := a
      have s1_5 : (a < 0 ∨ a = 0) ∨ 0 < a := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a))
      -- 1.6. cases, from 1.5
      have s1_6 : 0 ≤ a ^ (m + 1).toNat := by
        rcases s1_5 with (hC1 | hC2) | hC3
        · skip
          -- 1.6.1. inequalities, from C1
          have s1_6_1 : ¬ 0 ≤ a := by parley_side
          all_goals parley_side
        · skip
          -- 1.6.2. algebra, from C2
          have s1_6_2 : a ^ m.toNat * a = 0 := by linear_combination (norm := parley_norm) (a ^ m.toNat) * hC2
          -- 1.6.3. transitivity, from 1.6.2, 1.4
          have s1_6_3 : 0 = a ^ (m + 1).toNat := by parley_side
          -- 1.6.4. inequalities
          have s1_6_4 : 0 ≤ a ^ (m + 1).toNat := by parley_order
          all_goals parley_side
        · skip
          -- 1.6.5. mun:multiply-le x := 0, y := a^m, c := a, from C3, IH
          have s1_6_5 : a * 0 ≤ a * a ^ m.toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)); parley_side)
          -- 1.6.6. inequalities
          have s1_6_6 : 0 ≤ a ^ m.toNat * a := by parley_order
          -- 1.6.7. transitivity, from 1.6.6, 1.4
          have s1_6_7 : 0 ≤ a ^ (m + 1).toNat := by parley_order
          all_goals parley_side
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : 0 ≤ a ^ n.toNat := by first | (have h := (s1 n (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s1 n (by parley_side))] | (have h := (s1 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.PowerNonnegative.PowerNonnegative
