module

public import Tactics
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFillingAnItem

theorem a_range_bound_filling_an_item (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ n - k := by
  -- 1. mun:difference-nat0, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k) (le_trans (by norm_num) (Finset.mem_Icc.mp hH2).1) (n := n) hH1 (Finset.mem_Icc.mp hH2).2)

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFillingAnItem
