module

public import OrderTactics
public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.ValuesInARange

theorem values_in_a_range (n : ℤ) (hH1 : 0 < n) (m : ℤ) (hH2 : 0 < m) (f : ℤ → ℤ) (hH3 : Set.MapsTo f (Set.Icc (1 : ℤ) n : Set ℤ) (Set.Icc (1 : ℤ) m : Set ℤ)) (k : ℤ) (hH4 : k ∈ Finset.Icc (1 : ℤ) n) :
    f k ≤ f k := by
  -- 1. inequalities
  parley_order

end Parley.Tests.Elaborator.SetsADefineNames.ValuesInARange
