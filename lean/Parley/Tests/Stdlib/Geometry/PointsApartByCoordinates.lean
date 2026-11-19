module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.PointsApartByCoordinates

theorem points_apart_by_coordinates (A : ℂ) (B : ℂ) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH7 : A = Complex.mk a b) (hH8 : B = Complex.mk c d) :
    (A ≠ B ↔ ¬ ((a, b) : ℝ × ℝ) = (c, d)) := by
  -- 1. mun:geometry-points-apart-by-coordinates, from H7, H8
  exact (Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := A) (B := B) (a := a) (b := b) (c := c) (d := d) hH7 hH8)

end Parley.Tests.Stdlib.Geometry.PointsApartByCoordinates
