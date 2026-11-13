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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfFive

theorem one_of_a_range_of_five (k : ℤ) (hH1 : k ∈ Finset.Icc (0 : ℤ) (4 : ℤ)) :
    ((((k = 4 ∨ k = 0) ∨ 2 = k) ∨ k = 1) ∨ k = 1 + 2) := by
  -- 1. inspection, from H1
  (have h := hH1; norm_num [Finset.mem_Icc, Set.mem_Icc] at h; norm_cast at h; omega)

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfFive
