module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialAll

theorem binomial_all (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose m m : ℤ) = 1 := by
  -- 1. mun:counting-binomial-all n := m
  have s1 : (LeanBridges.Counting.choose m m : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.BinomialAll
