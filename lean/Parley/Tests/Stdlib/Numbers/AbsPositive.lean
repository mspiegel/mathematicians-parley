module

public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsPositive

theorem abs_positive (x : ℝ) (hH2 : x ≠ 0) :
    abs x > 0 := by
  -- 1. mun:numbers-abs-positive, from H2
  have hI : 0 < abs x := by parley_instance_cast (((Parley.Items.Stdlib.Numbers.mun_abs_positive (x := (x : ℂ)))).mp (by exact_mod_cast hH2))
  exact hI

end Parley.Tests.Stdlib.Numbers.AbsPositive
