module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfAListedPair

theorem one_of_a_listed_pair (a : ℝ) (b : ℝ) (x : ℝ) (hH3 : x ∈ ({a, b} : Set ℝ)) :
    (x = b ∨ a = x) := by
  -- 1. inspection, from H3
  parley_set_side

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfAListedPair
