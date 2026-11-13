module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfANamedRange

theorem one_of_a_named_range (S : Set ℤ) (hH1 : S ⊆ (Set.univ : Set ℤ)) (hH2 : S = (Set.Icc (3 : ℤ) (5 : ℤ) : Set ℤ)) (x : ℤ) (hH3 : x ∈ S) :
    ((x = 3 ∨ x = 4) ∨ x = 5) := by
  -- 1. inspection, from H2, H3
  (have h := hH3; norm_num [hH2, Finset.mem_Icc, Set.mem_Icc] at h; norm_cast at h; omega)

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfANamedRange
