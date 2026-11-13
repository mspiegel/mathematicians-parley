module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/inspection-of-a-range-below-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeAboutZero

theorem a_range_about_zero (n : ℤ) (hH2 : n ∈ Finset.Icc (-1 : ℤ) (1 : ℤ)) :
    ((n = -1 ∨ n = 0) ∨ n = 1) := by
  -- 1. inspection, from H2
  (have h := hH2; norm_num [Finset.mem_Icc, Set.mem_Icc] at h; norm_cast at h; omega)

end Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeAboutZero
