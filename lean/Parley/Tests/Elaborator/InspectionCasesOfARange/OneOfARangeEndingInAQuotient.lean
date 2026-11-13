module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
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

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeEndingInAQuotient

theorem one_of_a_range_ending_in_a_quotient (k : ℤ) (hH1 : 1 - 2 + 1 ≤ (k : ℚ) ∧ (k : ℚ) ≤ 6 / 3) :
    ((k = 0 ∨ k = 1) ∨ k = 2) := by
  -- 1. inspection, from H1
  (have h := hH1; norm_num [Finset.mem_Icc, Set.mem_Icc] at h; norm_cast at h; omega)

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeEndingInAQuotient
