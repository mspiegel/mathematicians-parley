module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.SignedAngleReal

theorem signed_angle_real (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : P ≠ Q) (hH5 : R ≠ Q) :
    Complex.arg ((R - Q) / (P - Q)) ≤ Real.pi := by
  -- 1. mun:geometry-signed-angle-real, from H4, H5
  exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_real_3 (P := P) (Q := Q) (R := R) hH4 hH5)

end Parley.Tests.Stdlib.Geometry.SignedAngleReal
