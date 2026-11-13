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

namespace Parley.Tests.Stdlib.Reasoning.DoubleNegation

theorem double_negation (x : ℝ) (hH2 : ¬ x ≠ 0) :
    x = 0 := by
  -- 1. mun:reasoning-double-negation P := x = 0, from H2
  exact (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2)

end Parley.Tests.Stdlib.Reasoning.DoubleNegation
