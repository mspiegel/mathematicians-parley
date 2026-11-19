module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.SignedAngleSum

theorem signed_angle_sum (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : P ≠ Q) (hH5 : Q ≠ R) (hH6 : P ≠ R) :
    Complex.arg ((P - Q) / (R - Q)) + Complex.arg ((Q - R) / (P - R)) + Complex.arg ((R - P) / (Q - P)) ∈ ({-Real.pi, Real.pi} : Set ℝ) := by
  -- 1. thm:geometry-signed-angle-sum, from H4, H5, H6
  exact (Parley.Items.Stdlib.Geometry.thm_signed_angle_sum (P := P) (Q := Q) (R := R) hH4 hH5 hH6)

end Parley.Tests.Stdlib.Geometry.SignedAngleSum
