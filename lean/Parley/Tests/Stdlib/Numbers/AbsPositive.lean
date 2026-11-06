module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsPositive

theorem abs_positive (x : ℝ) (hH2 : x ≠ 0) :
    abs x > 0 := by
  -- 1. mun:numbers-abs-positive, from H2
  have s1 : abs x > 0 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_abs_positive (x := (x : ℂ)))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_positive (x := (x : ℂ)))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_positive (x := (x : ℂ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_positive (x := (x : ℂ)))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsPositive
