module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.Absorption

theorem absorption (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) n) :
    (LeanBridges.Counting.choose (n + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose n k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by
  -- 1. thm:counting-absorption, from H2
  have s1 : (LeanBridges.Counting.choose (n + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose n k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by exact (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.Absorption
