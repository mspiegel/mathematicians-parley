module

public import Counting
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialOne

theorem binomial_one (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = m + 1 := by
  -- 1. mun:counting-binomial-one n := m + 1
  exact (Parley.Items.Stdlib.Counting.mun_binomial_one (n := m + 1) (add_nonneg (hH1) (by norm_num)))

end Parley.Tests.Stdlib.Counting.BinomialOne
