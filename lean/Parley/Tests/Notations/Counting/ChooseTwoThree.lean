module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.ChooseTwoThree

theorem choose_two_three :
    (LeanBridges.Counting.choose (2 : ℤ) (3 : ℤ) : ℤ) = 0 := by
  -- 1. contradiction
  have s1 : ¬ (3 : ℤ) ∈ Finset.Icc (0 : ℤ) (2 : ℤ) := by
    by_contra hc_hS
    have hS : (3 : ℤ) ∈ Finset.Icc (0 : ℤ) (2 : ℤ) := by parley_suppose hc_hS
    -- 1.1. mun:range-bounds a := 0, b := 2, k := 3, from S
    have s1_1 : (3 : ℤ) ≤ 2 := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) hS)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) hS); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) hS) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) hS); parley_side)
    -- 1.2. arithmetic
    have s1_2 : ¬ (3 : ℤ) ≤ 2 := by parley_arith
    all_goals parley_side
  -- 2. mun:binomial-outside n := 2, k := 3, from 1
  have s2 : (LeanBridges.Counting.choose (2 : ℤ) (3 : ℤ) : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (2 : ℤ)) (by parley_side) (k := (3 : ℤ)) s1)
  all_goals exact s2

end Parley.Tests.Notations.Counting.ChooseTwoThree
