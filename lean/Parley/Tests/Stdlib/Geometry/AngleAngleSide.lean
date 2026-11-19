module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.AngleAngleSide

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.AngleAngleSide

theorem angle_angle_side (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (hH7 : LeanBridges.Geometry.Triangle A B C) (hH8 : LeanBridges.Geometry.Triangle D E F) (hH9 : EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) (hH10 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F) (hH11 : dist B C = dist E F) :
    (dist A B = dist D E ∧ dist B C = dist E F ∧ dist C A = dist F D ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F D ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) := by
  -- 1. thm:geometry-angle-angle-side, from H7, H8, H9, H10, H11
  exact (Parley.Stdlib.Geometry.AngleAngleSide.angle_angle_side (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) hH7 hH8 hH9 hH10 hH11)

end Parley.Tests.Stdlib.Geometry.AngleAngleSide
