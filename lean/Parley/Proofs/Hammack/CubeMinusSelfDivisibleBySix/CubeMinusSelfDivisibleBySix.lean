module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Basic
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
public import Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive

/-! Written from proofs/hammack/cube-minus-self-divisible-by-six.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.CubeMinusSelfDivisibleBySix

theorem cube_minus_self_divisible_by_six (n : ℤ) (hH1 : 0 ≤ n) :
    (6 : ℤ) ∣ n ^ 3 - n := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (6 : ℤ) ∣ k ^ 3 - k := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (6 : ℤ) ∣ (0 ^ 3 : ℤ) := by parley_arith
      simpa only [sub_zero] using s1_1
    | succ k hK hIH =>
      -- 1.2. thm:six-divides-three-consecutive
      have s1_2 : (6 : ℤ) ∣ 3 * k * (k + 1) := by exact (Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive.six_divides_three_consecutive (k := k) (by parley_side))
      -- 1.3. mun:divides-sum d := 6, a := k³ − k, b := 3·k·(k + 1), from IH, 1.2
      have s1_3 : (6 : ℤ) ∣ k ^ 3 - k + 3 * k * (k + 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (6 : ℤ)) (a := k ^ 3 - k) (b := 3 * k * (k + 1)) hIH s1_2)
      -- 1.4. substitute
      have c1 : k ^ 3 - k + 3 * k * (k + 1) = (k + 1) ^ 3 - (k + 1) := by parley_ring
      have row1 : (6 : ℤ) ∣ (k + 1) ^ 3 - (k + 1) := by parley_subst_at c1 s1_3
      exact row1
  -- 2. instantiate k := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.CubeMinusSelfDivisibleBySix
