module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsZero

theorem abs_zero :
    (abs 0 : ℤ) = 0 := by
  -- 1. mun:numbers-abs-zero
  have s1 : (abs 0 : ℤ) = 0 := by exact Parley.Items.Stdlib.Numbers.mun_abs_zero
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsZero
