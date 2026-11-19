module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.GreaterAngleGreaterSide
public import Parley.Stdlib.Geometry.IsoscelesAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.TriangleInequalityStrict

theorem triangle_inequality_strict (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    dist P R < dist P Q + dist Q R := by
  -- 1. axi:distance-positive P := Q, Q := R, from H4
  have s1 : dist Q R > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := Q) (Q := R) hH4.2.1)
  -- 2. obtain D: mun:segment-extension A := P, B := Q, r := |QR|, from H4, 1
  obtain ⟨D, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := P) (B := Q) (r := dist Q R) hH4.1 s1)
  -- 3. restate 2
  have s3 : dist Q R = dist Q D := by exact s2c.symm
  -- 4. mun:triangle-extension P := R, R := P, S := D, from H4, 2
  have s4 : LeanBridges.Geometry.Triangle R Q D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := R) (Q := Q) (R := P) (S := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R Q P) s2b)
  -- 5. mun:triangle-not-on-line P := Q, Q := P, from H4
  have s5 : ¬ Q ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := Q) (Q := P) (R := R) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q P R))
  -- 6. mun:between-collinear R := Q, S := P, T := D, from 2
  have s6 : Collinear ℝ {D, Q, P} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := Q) (S := P) (T := D) s2b)
  -- 7. def:on-line P := D, A := P, B := Q, from H4, 6
  have s7 : D ∈ LeanBridges.Geometry.line P Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := P) (B := Q) (P := D) hH4.1)).mpr (by (have h := s6; rw [LeanBridges.Geometry.collinear_swap_13 D Q P] at h; exact h) : Collinear ℝ {P, Q, D})
  -- 8. mun:between-ends-apart R := Q, S := P, T := D, from 2
  have s8 : P ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := Q) (S := P) (T := D) s2b)
  -- 9. mun:off-line-through R := P, P := R, S := Q, X := D, from 5, 7, 8
  have s9 : ¬ D ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_through (P := R) (R := P) (S := Q) (X := D) s5 s7 (Ne.symm s8))
  -- 10. mun:triangle-off-line P := D, Q := P, from H4, 9
  have s10 : LeanBridges.Geometry.Triangle D P R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := P) (R := R) hH4.2.2.1 s9)
  -- 11. mun:angle-addition A := P, B := D, C := R, M := Q, from H4, 2, 10
  have s11 : EuclideanGeometry.angle P R Q + EuclideanGeometry.angle Q R D = EuclideanGeometry.angle P R D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := P) (B := D) (C := R) (M := Q) (by (have h := s10; rw [LeanBridges.Geometry.triangle_swap_12 D P R] at h; exact h) : LeanBridges.Geometry.Triangle P D R) s2b (Ne.symm hH4.2.1))
  -- 12. axi:angle-measure Q := R, R := Q, from H4
  have s12a : EuclideanGeometry.angle P R Q > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := P) (Q := R) (R := Q) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle P R Q))
  have s12b : EuclideanGeometry.angle P R Q < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := P) (Q := R) (R := Q) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle P R Q))
  -- 13. inequalities
  have s13 : EuclideanGeometry.angle P R Q + EuclideanGeometry.angle Q R D > EuclideanGeometry.angle Q R D := by linarith only [s12a]
  -- 14. restate 11
  have s14 : EuclideanGeometry.angle P R D = EuclideanGeometry.angle P R Q + EuclideanGeometry.angle Q R D := by exact s11.symm
  -- 15. calculation
  have s15 : EuclideanGeometry.angle P R D > EuclideanGeometry.angle P D R := by
    calc EuclideanGeometry.angle P R D = EuclideanGeometry.angle P R Q + EuclideanGeometry.angle Q R D := s14
      _ > EuclideanGeometry.angle Q R D := s13
      _ = EuclideanGeometry.angle Q D R := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := R) (B := D) (C := Q) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_23 R Q D] at h; exact h) : LeanBridges.Geometry.Triangle R D Q) s3)
      _ = EuclideanGeometry.angle P D R := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := D) (Q := P) (R := R) (S := Q) (by (have h := s2b; rw [sbtw_comm (x := P) (y := Q) (z := D)] at h; exact h) : Sbtw ℝ D Q P) s4.2.2.1 (Ne.symm hH4.2.1) (Ne.symm hH4.2.2.1))
  -- 16. mun:segment-addition Q := D, S := Q, from 2
  have s16 : dist P Q + dist Q D = dist P D := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := P) (Q := D) (S := Q) s2b)
  -- 17. calculation
  have s17 : dist P Q + dist Q R > dist P R := by
    calc dist P Q + dist Q R = dist P D := by linear_combination s3 + s16
      _ > dist P R := by exact (Parley.Stdlib.Geometry.GreaterAngleGreaterSide.greater_angle_greater_side (A := P) (B := R) (C := D) (by (have h := s10; rw [LeanBridges.Geometry.triangle_rot_231 D P R] at h; exact h) : LeanBridges.Geometry.Triangle P R D) s15)
  -- 18. inequalities
  linarith only [s17]

end Parley.Stdlib.Geometry.TriangleInequalityStrict
