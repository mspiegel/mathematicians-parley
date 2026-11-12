module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
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
    intro hS
    -- 1.1. mun:range-bounds a := 0, b := 2, k := 3, from S
    have s1_1 : (3 : ℤ) ≤ 2 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (2 : ℤ)) (k := (3 : ℤ)) hS)
    -- 1.2. arithmetic
    have s1_2 : ¬ (3 : ℤ) ≤ 2 := by parley_arith
    exact s1_2 s1_1
  -- 2. mun:binomial-outside n := 2, k := 3, from 1
  exact (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (2 : ℤ)) (by norm_num) (k := (3 : ℤ)) s1)

end Parley.Tests.Notations.Counting.ChooseTwoThree
