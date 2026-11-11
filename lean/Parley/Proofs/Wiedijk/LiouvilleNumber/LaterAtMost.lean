module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TailBound

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtMost

set_option maxHeartbeats 400000 in
theorem later_at_most (n : ℤ) (hH1 : 0 < n) :
    (∀ i : ℤ, 0 < i → i ≥ n → (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 2 / 2 ^ LeanBridges.Counting.factorial (n + 1)) := by
  -- 1. thm:tail-bound
  have s1 : ∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - 2 / 2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + j).toNat := by exact (Parley.Proofs.Wiedijk.LiouvilleNumber.TailBound.tail_bound (n := n) (by parley_side))
  -- 2. proof
  intro i hK
  intro hA
  -- 2.1. mun:difference-nat0 m := n, n := i, from A
  have s2_1 : 0 ≤ i - n := by exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := n) (by parley_side) (n := i) (by parley_side) hA)
  -- 2.2. mun:power-real a := 2, m := (n + 1)! + (i − n), from 2.1
  -- 2.3. mun:power-positive a := 2, m := (n + 1)! + (i − n)
  have r318_1 : (2 : ℤ) > 0 := by parley_arith
  have s2_3 : (2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) (by parley_side))
  set g : ℝ := (2 / 2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) : ℝ) with hD1
  have hD1_kind : True := by parley_side
  -- 2.4. instantiate j := i − n in line 1, from 2.1
  have s2_4 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + (i - n)), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - 2 / 2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) := by (have h := (s1 (i - n) (by parley_side)); simp only [parley_zpow_toNat (n := (LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) (h := add_nonneg (Nat.cast_nonneg _) (s2_1))] at h ⊢; exact_mod_cast h)
  -- 2.5. substitute
  have s2_5 : (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - g := by
    have c1 : n + (i - n) = i := by parley_ring
    have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - 2 / 2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) := by (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) t, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - 2 / 2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)))) c1 s2_4; push_cast at h ⊢; all_goals exact_mod_cast h)
    have c2 : 2 / 2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) = g := by (have h := congrArg (fun t : ℝ => t) (hD1).symm; push_cast at h ⊢; all_goals exact_mod_cast h)
    have row2 : (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - g := by parley_subst_at c2 row1
    exact row2
  -- 2.6. mun:quotient-positive x := 2, y := 2^((n + 1)! + (i − n)), from D1, 2.3
  have r335_1 : (2 : ℤ) > 0 := by parley_arith
  have s2_6 : g > 0 := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := (2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) : ℝ)) (by parley_side) (by parley_side))
  -- 2.7. inequalities
  have s2_7 : (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - g + (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℝ)) := by parley_order
  -- 2.8. inequalities
  have s2_8 : 0 ≤ g := by parley_order
  -- 2.9. inequalities, from 2.7, 2.8
  parley_order

end Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtMost
