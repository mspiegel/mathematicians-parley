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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.OrRight

theorem or_right (x : ℝ) (hH2 : x = 1) :
    (x = 0 ∨ x = 1) := by
  -- 1. mun:reasoning-or-right, from H2
  exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = 0) (Q := x = 1) hH2)

end Parley.Tests.Stdlib.Reasoning.OrRight
