module

public import Counting
public import FactorialTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialTwo

theorem binomial_two (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose m (2 : ℤ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  -- 1. mun:counting-binomial-two n := m
  exact (Parley.Items.Stdlib.Counting.mun_binomial_two (n := m) hH1)

end Parley.Tests.Stdlib.Counting.BinomialTwo
