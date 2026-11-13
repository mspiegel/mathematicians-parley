module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.FactorPositive

theorem factor_positive (u : ℝ) (v : ℝ) (hH3 : u ≥ 0) (hH4 : u * v > 0) :
    v > 0 := by
  -- 1. mun:numbers-factor-positive a := u, b := v, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := u) (b := v) hH3 hH4)

end Parley.Tests.Stdlib.Numbers.FactorPositive
