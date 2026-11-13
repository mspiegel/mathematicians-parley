module

public import AlgebraTactics
public import Functions
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct

/-! Written from proofs/setmm/bernoulli-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BernoulliInequality.BernoulliInequality

theorem bernoulli_inequality (A : ℝ) (hH2 : 0 ≤ A) (n : ℤ) (hH3 : 0 ≤ n) :
    (A - 1) * (n : ℝ) + 1 ≤ A ^ n.toNat := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (A - 1) * (k : ℝ) + 1 ≤ A ^ k.toNat := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. algebra
      have s1_1 : A ^ 0 = 1 := by parley_ring
      -- 1.2. inequalities
      have s1_2 : (A - 1) * 0 + 1 ≤ A ^ 0 := by linarith only [s1_1]
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_2
    | succ k hK hIH =>
      -- 1.3. mun:exponent-step a := A, m := k
      have s1_3 : A ^ (k + 1).toNat = A ^ k.toNat * A := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) hK)
      -- 1.4. inequalities
      have s1_4 : 0 ≤ A ^ k.toNat - ((A - 1) * (k : ℝ) + 1) := by linarith only [hIH]
      set X : ℝ := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1) with hD1
      -- 1.5. thm:nonnegative-product x := A, y := X, from D1, H2, 1.4
      have s1_5 : 0 ≤ A * X := by
        try simp only [hD1] at ⊢
        try push_cast at ⊢
        exact (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := A) (y := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1)) hH2 s1_4)
      -- 1.6. mun:square-nonneg x := A − 1
      have s1_6 : 0 ≤ (A - 1) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A - 1))
      -- 1.7. thm:nonnegative-product x := (A − 1)², y := k, from K, 1.6
      have s1_7 : 0 ≤ (A - 1) ^ 2 * (k : ℝ) := by exact (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := (A - 1) ^ 2) (y := (k : ℝ)) s1_6 (by exact_mod_cast ge_iff_le.mp hK))
      -- 1.8. algebra, from D1
      have s1_8 : A ^ k.toNat * A - ((A - 1) * ((k : ℝ) + 1) + 1) = A * X + (A - 1) ^ 2 * (k : ℝ) := by
        try simp only [hD1] at ⊢
        try push_cast at ⊢
        parley_ring
      -- 1.9. inequalities, from 1.5, 1.7
      have s1_9 : 0 ≤ A * X + (A - 1) ^ 2 * (k : ℝ) := by linarith only [s1_5, s1_7]
      -- 1.10. transitivity, from 1.9, 1.8
      have s1_10 : 0 ≤ A ^ k.toNat * A - ((A - 1) * ((k : ℝ) + 1) + 1) := by exact LE.le.trans_eq s1_9 s1_8.symm
      -- 1.11. inequalities
      have s1_11 : (A - 1) * ((k : ℝ) + 1) + 1 ≤ A ^ k.toNat * A := by linarith only [s1_10]
      -- 1.12. transitivity, from 1.11, 1.3
      have s1_12 : (A - 1) * ((k : ℝ) + 1) + 1 ≤ A ^ (k + 1).toNat := by exact LE.le.trans_eq s1_11 s1_3.symm
      exact_mod_cast s1_12
  -- 2. instantiate k := n in line 1
  exact (s1 n hH3)

end Parley.Proofs.Setmm.BernoulliInequality.BernoulliInequality
