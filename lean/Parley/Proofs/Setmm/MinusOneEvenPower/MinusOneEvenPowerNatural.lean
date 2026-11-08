module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/minus-one-even-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural

theorem minus_one_even_power_natural (n : ℤ) (hH1 : 0 ≤ n) :
    ((-1) ^ (2 * n).toNat : ℤ) = 1 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → ((-1) ^ (2 * k).toNat : ℤ) = 1 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      parley_arith
    | succ k hK hIH =>
      -- 1.2. algebra
      have s1_2 : 2 * (k + 1) = 2 * k + 1 + 1 := by parley_ring
      -- 1.3. calculation
      have s1_3 : ((-1) ^ (2 * k + 1).toNat : ℤ) = -1 := by
        calc ((-1) ^ (2 * k + 1).toNat : ℤ) = (-1) ^ (2 * k).toNat * -1 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side))
          _ = 1 * -1 := by parley_subst hIH
          _ = -1 := by norm_num
      -- 1.4. calculation
      calc ((-1) ^ (2 * (k + 1)).toNat : ℤ) = (-1) ^ (2 * k + 1 + 1).toNat := by parley_subst s1_2
        _ = (-1) ^ (2 * k + 1).toNat * -1 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side))
        _ = -1 * -1 := by parley_subst s1_3
        _ = 1 := by norm_num
  -- 2. instantiate k := n in line 1
  first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)

end Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural
