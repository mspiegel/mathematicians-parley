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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.ExteriorAngleGreater
public import Parley.Stdlib.Geometry.VerticalAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ExteriorAngleGreaterOther

theorem exterior_angle_greater_other (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : Sbtw ℝ B C D) (hH7 : LeanBridges.Geometry.Triangle A C D) :
    EuclideanGeometry.angle A C D > EuclideanGeometry.angle A B C := by
  -- 1. axi:distance-positive P := A, Q := C, from H5
  have s1 : dist A C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := A) (Q := C) hH5.2.2.1)
  -- 2. obtain E: mun:segment-extension B := C, r := |AC|, from H5, 1
  obtain ⟨E, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := A) (B := C) (r := dist A C) hH5.2.2.1 s1)
  -- 3. calculation
  have r211_1 : LeanBridges.Geometry.Triangle B C E := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := B) (Q := C) (R := A) (S := E) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) s2b)
  calc EuclideanGeometry.angle A C D = EuclideanGeometry.angle D C A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := D) (Q := C) (R := A) (Ne.symm hH7.2.1) hH7.1 (Ne.symm hH7.2.2.1)).symm
    _ = EuclideanGeometry.angle B C E := by exact (Parley.Stdlib.Geometry.VerticalAngles.vertical_angles (A := B) (B := E) (C := D) (D := A) (O := C) hH6 (by (have h := s2b; rw [sbtw_comm (x := A) (y := C) (z := E)] at h; exact h) : Sbtw ℝ E C A) r211_1 (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_13 A C D] at h; exact h) : LeanBridges.Geometry.Triangle D C A)).symm
    _ > EuclideanGeometry.angle A B C := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreater.exterior_angle_greater (A := B) (B := A) (C := C) (D := E) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) s2b r211_1)

end Parley.Stdlib.Geometry.ExteriorAngleGreaterOther
