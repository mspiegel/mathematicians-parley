module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/inspection-of-a-range-below-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeBelowZero

theorem a_range_below_zero (n : ℤ) (hH2 : n ∈ Finset.Icc (-2 : ℤ) (0 : ℤ)) :
    ((n = -2 ∨ n = -1) ∨ n = 0) := by
  -- 1. inspection, from H2
  (have h := hH2; norm_num [Finset.mem_Icc, Set.mem_Icc] at h; norm_cast at h; omega)

end Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeBelowZero
