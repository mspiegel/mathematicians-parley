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
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/docs/forbid.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Forbid.CongruentByAnAngle

theorem congruent_by_an_angle (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (hH7 : LeanBridges.Geometry.Triangle A B C) (hH8 : LeanBridges.Geometry.Triangle D E F) (hH9 : dist A B = dist D E) (hH10 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F) (hH11 : dist B C = dist E F) :
    (dist A B = dist D E ∧ dist B C = dist E F ∧ dist C A = dist F D ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F D ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) := by
  -- 1. axi:side-angle-side P := A, Q := B, R := C, P′ := D, Q′ := E, R′ := F, from H7, H8, H9, H10, H11
  exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := A) (P' := D) (Q := B) (Q' := E) (R := C) (R' := F) hH7 hH8 hH9 hH10 hH11)

end Parley.Tests.Docs.Forbid.CongruentByAnAngle
