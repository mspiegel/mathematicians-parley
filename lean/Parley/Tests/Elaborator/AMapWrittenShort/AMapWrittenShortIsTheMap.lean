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

/-! Written from tests/elaborator/a-map-written-short.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapWrittenShort.AMapWrittenShortIsTheMap

theorem a_map_written_short_is_the_map (x : ℝ) (hH2 : (fun y : ℝ => y + 1) x = 3) :
    (fun y : ℝ => y + 1) x = 3 := by
  -- 1. restate H2
  exact hH2

end Parley.Tests.Elaborator.AMapWrittenShort.AMapWrittenShortIsTheMap
