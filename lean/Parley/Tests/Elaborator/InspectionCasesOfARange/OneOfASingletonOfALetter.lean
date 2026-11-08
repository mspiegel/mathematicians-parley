module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingletonOfALetter

theorem one_of_a_singleton_of_a_letter (a : ℝ) (x : ℝ) (hH2 : x ∈ ({a} : Set ℝ)) :
    x = a := by
  -- 1. inspection, from H2
  parley_set_side

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingletonOfALetter
