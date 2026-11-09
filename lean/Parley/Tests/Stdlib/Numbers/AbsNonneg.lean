module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsNonneg

theorem abs_nonneg (x : ℝ) :
    abs x ≥ 0 := by
  -- 1. mun:numbers-abs-nonneg
  exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ)))

end Parley.Tests.Stdlib.Numbers.AbsNonneg
