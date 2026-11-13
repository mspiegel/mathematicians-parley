module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
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

/-! Written from tests/elaborator/a-define-on-an-open-interval.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineOnAnOpenInterval.ADefineOnAnOpenInterval

theorem a_define_on_an_open_interval (a : ℝ) (b : ℝ) (h : ℝ → ℝ) (hD1 : ∀ t : ℝ, t ∈ (Set.Ioo a b : Set ℝ) → h t = t + 1) :
    True := by
  -- 1. D1
  exact trivial

end Parley.Tests.Elaborator.ADefineOnAnOpenInterval.ADefineOnAnOpenInterval
