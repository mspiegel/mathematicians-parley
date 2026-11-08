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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/power-above-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerAboveOne.PowerAboveOne

theorem power_above_one (A : ℝ) (hH2 : 1 < A) (n : ℤ) (hH3 : 0 < n) :
    1 < A ^ n.toNat := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → 1 < A ^ k.toNat := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. restate H2
      have s1_1 : 1 < A ^ 1 := by parley_side
      simpa using s1_1
    | succ k hK hIH =>
      -- 1.2. inequalities
      have s1_2 : 1 ≤ A ^ k.toNat := by parley_order
      -- 1.3. inequalities, from H2
      have s1_3 : 0 < A := by parley_order
      -- 1.4. mun:multiply-le x := 1, y := A^k, c := A, from 1.2, 1.3
      have s1_4 : A * 1 ≤ A * A ^ k.toNat := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := A ^ k.toNat) (c := A) (by parley_side) (by parley_side))
      -- 1.5. inequalities
      have s1_5 : A ≤ A * A ^ k.toNat := by parley_order
      -- 1.6. transitivity, from H2, 1.5
      have s1_6 : 1 < A * A ^ k.toNat := by parley_order
      -- 1.7. calculation
      calc (1 : ℝ) < A * A ^ k.toNat := by first | parley_side | parley_line_toNat s1_6
        _ = A ^ k.toNat * A := by parley_ring
        _ = A ^ (k + 1).toNat := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)).symm
  -- 2. instantiate k := n in line 1
  first | (have h := (s1 n (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s1 n (by parley_side))] | (have h := (s1 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); parley_side)

end Parley.Proofs.Setmm.PowerAboveOne.PowerAboveOne
