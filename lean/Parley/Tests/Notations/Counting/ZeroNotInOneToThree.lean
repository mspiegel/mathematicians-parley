module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.ZeroNotInOneToThree

theorem zero_not_in_one_to_three :
    ¬ (0 : ℤ) ∈ Finset.Icc (1 : ℤ) (3 : ℤ) := by
  -- 1. arithmetic
  have s1 : ¬ (0 : ℤ) < 0 := by parley_arith
  -- 2. contradiction
  intro hS
  -- 2.1. def:range n := 3, k := 0, from S
  have s2_1 : (0 : ℤ) < 0 := by exact (((Parley.Items.Stdlib.Sums.def_range (k := (0 : ℤ)) (n := (3 : ℤ)))).mp hS).1
  exact s1 s2_1

end Parley.Tests.Notations.Counting.ZeroNotInOneToThree
