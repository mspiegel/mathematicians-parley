module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtLeast

theorem later_at_least (n : ℤ) (hH1 : 0 < n) :
    (∀ i : ℤ, 0 < i → i ≥ n + 1 → (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) := by
  -- 1. thm:partial-sums-increase n := n + 1
  have s1 : ∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1 + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by exact (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumsIncrease.partial_sums_increase (n := n + 1) (by parley_side))
  -- 2. proof
  intro i hK
  intro hA
  -- 2.1. mun:difference-nat0 m := n + 1, n := i, from A
  have s2_1 : 0 ≤ i - (n + 1) := by exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := n + 1) (by parley_side) (n := i) (le_of_lt hK) hA)
  -- 2.2. instantiate j := i − (n + 1) in line 1, from 2.1
  have s2_2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1 + (i - (n + 1))), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by exact (s1 (i - (n + 1)) s2_1)
  -- 2.3. substitute
  have c1 : n + 1 + (i - (n + 1)) = i := by parley_ring
  have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) i, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) t, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)))) c1 s2_2; push_cast at h ⊢; all_goals exact_mod_cast h)
  exact row1

end Parley.Proofs.Wiedijk.LiouvilleNumber.LaterAtLeast
