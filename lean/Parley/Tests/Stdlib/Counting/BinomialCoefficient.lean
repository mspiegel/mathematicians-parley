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

namespace Parley.Tests.Stdlib.Counting.BinomialCoefficient

theorem binomial_coefficient (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH3 : k ∈ Finset.Icc (0 : ℤ) n) :
    (LeanBridges.Counting.choose n k : ℚ) = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) := by
  -- 1. def:C, from H3
  exact (Parley.Items.Stdlib.Counting.def_C_2 (n := n) hH1 (k := k)) hH3

end Parley.Tests.Stdlib.Counting.BinomialCoefficient
