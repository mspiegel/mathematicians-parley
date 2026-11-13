module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
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

/-! Written from tests/elaborator/a-set-valued-define-sized.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted

theorem first_numbers_counted (m : ℤ) (hH1 : 0 ≤ m) :
    ((Set.Icc (1 : ℤ) m : Set ℤ).ncard : ℤ) = m := by
  -- 1. mun:range-size n := m, from D1
  exact (Parley.Items.Stdlib.Counting.mun_range_size (n := m) hH1)

end Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted
