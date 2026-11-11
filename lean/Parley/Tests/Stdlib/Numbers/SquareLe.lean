module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.SquareLe

theorem square_le (x : ℝ) (y : ℝ) (hH3 : x ≥ 0) (hH4 : y ≥ 0) :
    (x ≤ y ↔ x ^ 2 ≤ y ^ 2) := by
  -- 1. mun:numbers-square-le, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) hH3 hH4)

end Parley.Tests.Stdlib.Numbers.SquareLe
