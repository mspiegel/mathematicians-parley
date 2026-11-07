module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialOne

theorem binomial_one (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = m + 1 := by
  -- 1. mun:counting-binomial-one n := m + 1
  have s1 : (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = m + 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.BinomialOne
