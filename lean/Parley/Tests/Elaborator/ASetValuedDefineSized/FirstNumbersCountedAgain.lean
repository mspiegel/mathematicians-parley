module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted

/-! Written from tests/elaborator/a-set-valued-define-sized.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCountedAgain

theorem first_numbers_counted_again (m : ℤ) (hH1 : 0 ≤ m) :
    ((Set.Icc (1 : ℤ) m : Set ℤ).ncard : ℤ) = m := by
  -- 1. thm:first-numbers-counted
  have s1 : ((Set.Icc (1 : ℤ) m : Set ℤ).ncard : ℤ) = m := by exact (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m) (by parley_set_side))
  all_goals exact s1

end Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCountedAgain
