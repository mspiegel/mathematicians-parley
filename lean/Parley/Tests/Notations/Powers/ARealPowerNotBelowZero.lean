module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerNotBelowZero

theorem a_real_power_not_below_zero (x : ℝ) (hH2 : x ≥ 0) :
    x ^ (1 / 3 : ℝ) ≥ 0 := by
  -- 1. mun:real-power-nonneg y := 1/3, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_real_power_nonneg (x := x) hH2 (y := (1 / 3 : ℝ)))

end Parley.Tests.Notations.Powers.ARealPowerNotBelowZero
