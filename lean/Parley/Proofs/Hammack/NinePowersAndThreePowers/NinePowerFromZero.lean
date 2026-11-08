module

public import ArithTactics
public import Functions
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/nine-powers-and-three-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero

theorem nine_power_from_zero (n : ℤ) (hH1 : 0 ≤ n) :
    (9 ^ n.toNat : ℤ) = 3 ^ n.toNat * 3 ^ n.toNat := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (9 ^ k.toNat : ℤ) = 3 ^ k.toNat * 3 ^ k.toNat := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (9 ^ 0 : ℤ) = 3 ^ 0 * 3 ^ 0 := by parley_arith
      simpa only [Int.reduceToNat] using s1_1
    | succ k hK hIH =>
      -- 1.2. mun:exponent-step a := 9, m := k
      have s1_2 : (9 ^ (k + 1).toNat : ℤ) = 9 ^ k.toNat * 9 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (9 : ℤ)) (m := k) (by parley_side))
      -- 1.3. mun:exponent-step a := 3, m := k
      have s1_3 : (3 ^ (k + 1).toNat : ℤ) = 3 ^ k.toNat * 3 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side))
      -- 1.4. algebra, from IH, 1.2, 1.3
      linear_combination (norm := parley_norm) (9) * hIH + s1_2 + (-3 ^ (k + 1).toNat - 3 * 3 ^ k.toNat) * s1_3
  -- 2. instantiate k := n in line 1
  first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)

end Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero
