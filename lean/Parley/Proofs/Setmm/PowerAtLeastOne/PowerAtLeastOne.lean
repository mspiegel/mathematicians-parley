module

public import AlgebraTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/power-at-least-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerAtLeastOne.PowerAtLeastOne

theorem power_at_least_one (a : ℝ) (n : ℤ) (hH2 : 0 ≤ n) (hH3 : 1 ≤ a) :
    1 ≤ a ^ n.toNat := by
  -- 1. inequalities, from H3
  have s1 : a > 0 := by parley_order
  -- 2. induction on m starting at 0
  have s2 : ∀ m : ℤ, 0 ≤ m → 1 ≤ a ^ m.toNat := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. algebra
      have s2_1 : a ^ 0 = 1 := by parley_ring
      -- 2.2. inequalities
      have s2_2 : 1 ≤ a ^ 0 := by parley_order
      all_goals parley_side
    | succ m hK hIH =>
      -- 2.3. mun:exponent-step
      have s2_3 : a ^ (m + 1).toNat = a ^ m.toNat * a := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m) (by parley_side))
      -- 2.4. mun:multiply-le x := 1, y := a^m, c := a, from IH, 1
      have s2_4 : a * 1 ≤ a * a ^ m.toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m.toNat) (c := a) (by parley_side) (by parley_side)); parley_side)
      -- 2.5. inequalities
      have s2_5 : a ≤ a ^ m.toNat * a := by parley_order
      -- 2.6. transitivity, from H3, 2.5, 2.3
      have s2_6 : 1 ≤ a ^ (m + 1).toNat := by parley_order
      all_goals parley_side
  -- 3. instantiate m := n in line 2
  have s3 : 1 ≤ a ^ n.toNat := by first | (have h := (s2 n (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s2 n (by parley_side))] | (have h := (s2 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s2 n (by parley_side)) | (have h := (s2 n (by parley_side)); parley_side)
  all_goals exact s3

end Parley.Proofs.Setmm.PowerAtLeastOne.PowerAtLeastOne
