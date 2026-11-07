module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-function-type-widened.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionTypeWidened.AFunctionTypeWidened

theorem a_function_type_widened (n : ℤ) (hH1 : 0 < n) (t : ℤ → ℤ) (hH2 : Set.MapsTo t (Set.Icc (1 : ℤ) n : Set ℤ) {n : ℤ | 0 < n}) :
    True := by
  -- 1. mun:product-real a := 1, b := n
  all_goals parley_set_side

end Parley.Tests.Elaborator.AFunctionTypeWidened.AFunctionTypeWidened
