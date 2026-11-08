module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/cubic-plus-multiple-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubicPlusMultipleOfThree.CubicPlusMultipleOfThree

theorem cubic_plus_multiple_of_three (n : ℤ) (hH1 : 0 ≤ n) :
    (3 : ℤ) ∣ n ^ 3 + 5 * n + 6 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (3 : ℤ) ∣ k ^ 3 + 5 * k + 6 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      parley_arith
    | succ k hK hIH =>
      -- 1.2. mun:divides-self n := 3
      have s1_2 : (3 : ℤ) ∣ (3 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (3 : ℤ)))
      -- 1.3. mun:divides-multiple e := 3, a := 3, x := k² + k + 2, from 1.2
      have s1_3 : (3 : ℤ) ∣ 3 * (k ^ 2 + k + 2) := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (3 : ℤ)) (x := k ^ 2 + k + 2) s1_2)
      -- 1.4. mun:divides-sum d := 3, a := k³ + 5k + 6, b := 3·(k² + k + 2), from IH, 1.3
      have s1_4 : (3 : ℤ) ∣ k ^ 3 + 5 * k + 6 + 3 * (k ^ 2 + k + 2) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := k ^ 3 + 5 * k + 6) (b := 3 * (k ^ 2 + k + 2)) hIH s1_3)
      -- 1.5. substitute
      have c1 : k ^ 3 + 5 * k + 6 + 3 * (k ^ 2 + k + 2) = (k + 1) ^ 3 + 5 * (k + 1) + 6 := by parley_ring
      have row1 : (3 : ℤ) ∣ (k + 1) ^ 3 + 5 * (k + 1) + 6 := by parley_subst_at c1 s1_4
      exact row1
  -- 2. instantiate k := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.CubicPlusMultipleOfThree.CubicPlusMultipleOfThree
