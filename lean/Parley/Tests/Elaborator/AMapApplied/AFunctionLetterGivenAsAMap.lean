module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Functions
public import Parley.Tests.Elaborator.AMapApplied.AValueAssumed

/-! Written from tests/elaborator/a-map-applied.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapApplied.AFunctionLetterGivenAsAMap

theorem a_function_letter_given_as_a_map (x : ℝ) (hH2 : x + 1 = 3) :
    x + 1 = 3 := by
  -- 1. membership
  -- 2. thm:a-value-assumed f := (the map sending y ∈ ℝ to y + 1), from H2
  exact (Parley.Tests.Elaborator.AMapApplied.AValueAssumed.a_value_assumed (f := (fun y : ℝ => y + 1)) (x := x) hH2)

end Parley.Tests.Elaborator.AMapApplied.AFunctionLetterGivenAsAMap
