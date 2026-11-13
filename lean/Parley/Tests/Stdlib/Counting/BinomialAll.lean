module

public import Counting
public import FactorialTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialAll

theorem binomial_all (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose m m : ℤ) = 1 := by
  -- 1. mun:counting-binomial-all n := m
  exact (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) hH1)

end Parley.Tests.Stdlib.Counting.BinomialAll
