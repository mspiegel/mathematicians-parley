module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsSquare

theorem abs_square (x : ℝ) :
    abs x ^ 2 = x ^ 2 := by
  -- 1. mun:numbers-abs-square
  have s1 : abs x ^ 2 = x ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsSquare
