module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerUnderABinder

theorem a_real_power_under_a_binder :
    (∀ y : ℝ, (2 : ℝ) ^ y > 0) := by
  -- 1. proof
  intro y
  -- 1.1. mun:real-power-positive x := 2
  have r65_1 : (2 : ℤ) > 0 := by norm_num
  exact (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := (2 : ℝ)) (by norm_num) (y := y))

end Parley.Tests.Notations.Powers.ARealPowerUnderABinder
