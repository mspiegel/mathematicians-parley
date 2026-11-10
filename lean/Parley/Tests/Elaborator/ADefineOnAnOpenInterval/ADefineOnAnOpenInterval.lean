module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-define-on-an-open-interval.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineOnAnOpenInterval.ADefineOnAnOpenInterval

theorem a_define_on_an_open_interval (a : ℝ) (b : ℝ) (h : ℝ → ℝ) (hD1 : ∀ t : ℝ, t ∈ (Set.Ioo a b : Set ℝ) → h t = t + 1) :
    True := by
  -- 1. D1
  exact trivial

end Parley.Tests.Elaborator.ADefineOnAnOpenInterval.ADefineOnAnOpenInterval
