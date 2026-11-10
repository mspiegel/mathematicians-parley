module

public import ArithTactics
public import Functions
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf

/-! Written from proofs/hammack/five-divides-power-of-two-multiple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesPowerOfTwoMultiple

theorem five_divides_power_of_two_multiple (a : ℤ) (n : ℤ) (hH2 : 0 < n) (hH3 : (5 : ℤ) ∣ 2 ^ n.toNat * a) :
    (5 : ℤ) ∣ a := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (∀ c : ℤ, (5 : ℤ) ∣ 2 ^ k.toNat * c → (5 : ℤ) ∣ c) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      intro c
      intro hA
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 0 : ℤ) = 1 := by parley_arith
      -- 1.2. substitute 2^0 = 1 (line 1.1) into A
      have s1_2 : (5 : ℤ) ∣ 1 * c := by (have h := Eq.subst (motive := (fun t : ℤ => (5 : ℤ) ∣ t * c)) s1_1 hA; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.3. restate 1.2
      parley_side
    | succ k hK hIH =>
      intro c
      intro hA
      -- 1.4. mun:exponent-step a := 2, m := k
      have s1_4 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) (by parley_side))
      -- 1.5. algebra, from 1.4
      have s1_5 : 2 ^ (k + 1).toNat * c = 2 ^ k.toNat * (2 * c) := by linear_combination (norm := parley_norm) (c) * s1_4
      -- 1.6. substitute 2^(k + 1)·c = 2^k·(2·c) (line 1.5) into A
      have s1_6 : (5 : ℤ) ∣ 2 ^ k.toNat * (2 * c) := by (have h := Eq.subst (motive := (fun t : ℤ => (5 : ℤ) ∣ t)) s1_5 hA; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.7. instantiate c := 2·c in IH, from 1.6
      have s1_7 : (5 : ℤ) ∣ 2 * c := by exact (hIH (2 * c) (by parley_side))
      -- 1.8. thm:five-divides-half b := c, from 1.7
      exact (Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf.five_divides_half (b := c) s1_7)
  -- 2. instantiate k := n, c := a in line 1, from H3
  exact (s1 n (by parley_side) a (by parley_side))

end Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesPowerOfTwoMultiple
