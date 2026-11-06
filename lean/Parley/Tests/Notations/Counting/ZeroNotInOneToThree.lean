module

public import ArithTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.ZeroNotInOneToThree

theorem zero_not_in_one_to_three :
    ¬ (0 : ℤ) ∈ Finset.Icc (1 : ℤ) (3 : ℤ) := by
  -- 1. arithmetic
  have s1 : ¬ (0 : ℤ) < 0 := by parley_arith
  -- 2. contradiction
  have s2 : ¬ (0 : ℤ) ∈ Finset.Icc (1 : ℤ) (3 : ℤ) := by
    by_contra hc_hS
    have hS : (0 : ℤ) ∈ Finset.Icc (1 : ℤ) (3 : ℤ) := by parley_suppose hc_hS
    -- 2.1. def:range n := 3, k := 0, from S
    have s2_1 : (0 : ℤ) < 0 := by first | exact (((Parley.Items.Stdlib.Sums.def_range (k := (0 : ℤ)) (n := (3 : ℤ)))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sums.def_range (k := (0 : ℤ)) (n := (3 : ℤ)))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sums.def_range (k := (0 : ℤ)) (n := (3 : ℤ)))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sums.def_range (k := (0 : ℤ)) (n := (3 : ℤ)))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sums.def_range (k := (0 : ℤ)) (n := (3 : ℤ)))).mp (by parley_side)).1; parley_side)
    all_goals parley_side
  all_goals exact s2

end Parley.Tests.Notations.Counting.ZeroNotInOneToThree
