module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
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
public import Parley.Stdlib.Geometry.IsoscelesAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.IsoscelesBasePoint

theorem isosceles_base_point (D : ℂ) (G : ℂ) (E : ℂ) (X : ℂ) (hH5 : LeanBridges.Geometry.Triangle D G E) (hH6 : dist E D = dist E G) (hH7 : Sbtw ℝ D X G) (hH8 : LeanBridges.Geometry.Triangle E D X) :
    EuclideanGeometry.angle E D X = EuclideanGeometry.angle E G X := by
  -- 1. mun:between-apart R := X, S := D, T := G, from H7
  have s1a : D ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := X) (S := D) (T := G) hH7)
  have s1b : G ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := X) (S := D) (T := G) hH7)
  -- 2. calculation
  calc EuclideanGeometry.angle E D X = EuclideanGeometry.angle X D E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := D) (R := X) hH8.1 (Ne.symm hH8.2.1) hH8.2.2.1)
    _ = EuclideanGeometry.angle G D E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := D) (Q := G) (R := E) (S := X) hH7 (Ne.symm hH5.2.2.1) hH8.2.2.1 (Ne.symm hH5.2.1))
    _ = EuclideanGeometry.angle E D G := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := G) (Q := D) (R := E) (Ne.symm hH5.1) (Ne.symm hH5.2.2.1) hH5.2.1)
    _ = EuclideanGeometry.angle E G D := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := D) (B := G) (C := E) hH5 hH6)
    _ = EuclideanGeometry.angle D G E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := G) (R := D) (Ne.symm hH5.2.1) hH5.1 (Ne.symm hH5.2.2.1))
    _ = EuclideanGeometry.angle X G E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := G) (Q := D) (R := E) (S := X) (by (have h := hH7; rw [sbtw_comm (x := D) (y := X) (z := G)] at h; exact h) : Sbtw ℝ G X D) (Ne.symm hH5.2.1) hH8.2.2.1 (Ne.symm hH5.2.2.1)).symm
    _ = EuclideanGeometry.angle E G X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := G) (R := E) (Ne.symm s1b) (Ne.symm hH5.2.1) (Ne.symm hH8.2.2.1))

end Parley.Stdlib.Geometry.IsoscelesBasePoint
