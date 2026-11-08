module

public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/factorial-plus-k-not-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FactorialPlusKNotPrime.FactorialPlusKNotPrime

set_option maxHeartbeats 400000 in
theorem factorial_plus_k_not_prime (n : ℤ) (hH1 : 0 < n) (k : ℤ) (hH2 : k ∈ Finset.Icc (2 : ℤ) n) :
    ¬ Nat.Prime ((LeanBridges.Counting.factorial n : ℤ) + k).toNat := by
  -- 1. mun:range-bounds a := 2, b := n, from H2
  have s1a : 2 ≤ k := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := n) (k := k) hH2)
  have s1b : k ≤ n := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := n) (k := k) hH2)
  -- 2. inequalities, from 1
  have s2 : 0 < k := by parley_order
  -- 3. mun:pos-int-nat m := k, from 2
  have s3 : 0 < k := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) s2)
  -- 4. mun:factorial-nat
  have s4 : 0 < (LeanBridges.Counting.factorial n : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (by parley_side))
  -- 5. mun:nat-closure a := n!, b := k, from 3
  have s5 : 0 < (LeanBridges.Counting.factorial n : ℤ) + k := by exact (Parley.Items.Stdlib.Numbers.mun_nat_closure_1 (a := (LeanBridges.Counting.factorial n : ℤ)) (by parley_side) (b := k) (by parley_side))
  -- 6. mun:factorial-divisible m := k, from 1, 3
  have s6 : k ∣ (LeanBridges.Counting.factorial n : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := k) (by parley_side) s1b)
  -- 7. mun:divides-self n := k
  have s7 : k ∣ k := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := k))
  -- 8. mun:divides-sum d := k, a := n!, b := k, from 6, 7
  have s8 : k ∣ (LeanBridges.Counting.factorial n : ℤ) + k := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := k) (a := (LeanBridges.Counting.factorial n : ℤ)) (b := k) s6 s7)
  -- 9. contradiction
  intro hS
  -- 9.1. def:prime p := n! + k, from S
  have r47_1 : 0 < (LeanBridges.Counting.factorial n : ℤ) + k := by parley_side
  have s9_1a : (LeanBridges.Counting.factorial n : ℤ) + k > 1 := (((Parley.Items.Stdlib.Divisibility.def_prime (p := (LeanBridges.Counting.factorial n : ℤ) + k) (by parley_side))).mp hS).1
  have s9_1b : ∀ d : ℤ, 0 < d → d ∣ (LeanBridges.Counting.factorial n : ℤ) + k → d = 1 ∨ d = (LeanBridges.Counting.factorial n : ℤ) + k := (((Parley.Items.Stdlib.Divisibility.def_prime (p := (LeanBridges.Counting.factorial n : ℤ) + k) (by parley_side))).mp hS).2
  -- 9.2. instantiate d := k in line 9.1, from 3
  have s9_2 : k ∣ (LeanBridges.Counting.factorial n : ℤ) + k → k = 1 ∨ k = (LeanBridges.Counting.factorial n : ℤ) + k := by first | exact (s9_1b k (by parley_side)) | exact ((s9_1b k (by parley_side))).symm | simpa using (s9_1b k (by parley_side)) | exact_mod_cast (s9_1b k (by parley_side)) | (have h := (s9_1b k (by parley_side)); parley_side)
  -- 9.3. mun:modus-ponens P := k divides n! + k, from 8, 9.2
  have s9_3 : k = 1 ∨ k = (LeanBridges.Counting.factorial n : ℤ) + k := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := k ∣ (LeanBridges.Counting.factorial n : ℤ) + k) (Q := k = 1 ∨ k = (LeanBridges.Counting.factorial n : ℤ) + k) s9_2 s8)
  -- 9.4. cases, from 9.3
  have s9_4 : k = (LeanBridges.Counting.factorial n : ℤ) + k := by
    rcases s9_3 with hC1 | hC2
    · skip
      -- 9.4.1. inequalities, from 1
      have s9_4_1 : 1 < k := by parley_order
      -- 9.4.2. inequalities
      have s9_4_2 : 1 ≠ k := by parley_side
      exact absurd hC1.symm s9_4_2
    · skip
      exact hC2
  -- 9.5. algebra, from 9.4
  have s9_5 : (LeanBridges.Counting.factorial n : ℤ) = 0 := by linear_combination (norm := parley_norm) (-1) * s9_4
  -- 9.6. inequalities, from 4
  have s9_6 : (LeanBridges.Counting.factorial n : ℤ) ≠ 0 := by parley_side
  exact s9_6 s9_5

end Parley.Proofs.Hammack.FactorialPlusKNotPrime.FactorialPlusKNotPrime
