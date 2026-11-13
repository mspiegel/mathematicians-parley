module

public import Counting
public import FactorialTactics
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-last-term-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALastTermWithoutItsZero.ALastTermWithoutItsZero

theorem a_last_term_without_its_zero :
    (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. mun:sum-last n := 0, from 1
  have hI : (∑ a ∈ Finset.Icc (0 : ℤ) (0 + 1 : ℤ), ((LeanBridges.Counting.choose (1 - a) a : ℤ) : ℤ)) = (∑ a ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - a) a : ℤ) : ℤ)) + (LeanBridges.Counting.choose (1 - (0 + 1) : ℤ) (0 + 1 : ℤ) : ℤ) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by norm_num)))
  simpa only [Int.cast_one, Int.cast_zero, zero_add] using hI

end Parley.Tests.Elaborator.ALastTermWithoutItsZero.ALastTermWithoutItsZero
