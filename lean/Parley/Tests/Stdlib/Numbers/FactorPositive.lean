module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.FactorPositive

theorem factor_positive (u : ℝ) (v : ℝ) (hH3 : u ≥ 0) (hH4 : u * v > 0) :
    v > 0 := by
  -- 1. mun:numbers-factor-positive a := u, b := v, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := u) (b := v) hH3 (by parley_side))

end Parley.Tests.Stdlib.Numbers.FactorPositive
