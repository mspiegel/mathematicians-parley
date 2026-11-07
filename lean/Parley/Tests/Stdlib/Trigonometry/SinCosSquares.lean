module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SinCosSquares

theorem sin_cos_squares (a : ℂ) :
    Complex.sin a ^ 2 + Complex.cos a ^ 2 = 1 := by
  -- 1. mun:trigonometry-sin-cos-squares
  have s1 : Complex.sin a ^ 2 + Complex.cos a ^ 2 = 1 := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a))
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.SinCosSquares
