module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/an-area-weakened.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnAreaWeakened.AnAreaWeakened

theorem an_area_weakened (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : A ≠ C) (hH5 : B ≠ C) (hH6 : 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) > 0) (hH7 : (1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) ^ 2 = 1 ^ 2) :
    1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) = 1 := by
  -- 1. mun:area-real P := A, Q := B, R := C, from H4, H5
  -- 2. mun:square-equal x := the area of △ABC, y := 1, from H7
  have r20_2 : 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) ≥ 0 := by linarith only [hH6]
  have r20_3 : (1 : ℤ) ≥ 0 := by norm_num
  exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := 1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C))))) (y := (1 : ℝ)) r20_2 (by norm_num))).mp hH7

end Parley.Tests.Elaborator.AnAreaWeakened.AnAreaWeakened
