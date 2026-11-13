module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Tauto

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfAListedPair

theorem one_of_a_listed_pair (a : ℝ) (b : ℝ) (x : ℝ) (hH3 : x ∈ ({a, b} : Set ℝ)) :
    (x = b ∨ a = x) := by
  -- 1. inspection, from H3
  (have h := hH3; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; tauto)

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfAListedPair
