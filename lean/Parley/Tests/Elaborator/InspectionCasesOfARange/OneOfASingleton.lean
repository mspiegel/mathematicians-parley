module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Tauto

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingleton

theorem one_of_a_singleton (x : ℤ) (hH1 : x ∈ ({(3 : ℤ)} : Set ℤ)) :
    x = 3 := by
  -- 1. inspection, from H1
  (have h := hH1; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; tauto)

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingleton
