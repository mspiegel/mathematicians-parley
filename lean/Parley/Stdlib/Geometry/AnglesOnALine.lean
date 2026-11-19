module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
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
public import Parley.Items.Stdlib.Geometry

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AnglesOnALine

theorem angles_on_a_line (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (T : ℂ) (hH6 : Sbtw ℝ S R T) (hH7 : 0 < Complex.im ((P - R) / (S - R)) * Complex.im ((Q - R) / (S - R))) (hH8 : Complex.im ((S - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0) (hH9 : LeanBridges.Geometry.Triangle Q R T) :
    EuclideanGeometry.angle S R P + EuclideanGeometry.angle P R Q + EuclideanGeometry.angle T R Q = (180 : ℝ) * Real.pi / 180 := by
  -- 1. mun:same-side-off-line A := R, B := S, from H7
  have s1a : R ≠ S := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_1 (A := R) (B := S) (P := P) (Q := Q) hH7)
  have s1b : ¬ P ∈ LeanBridges.Geometry.line R S := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := R) (B := S) (P := P) (Q := Q) hH7)
  have s1c : ¬ Q ∈ LeanBridges.Geometry.line R S := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := R) (B := S) (P := P) (Q := Q) hH7)
  -- 2. mun:opposite-sides-off-line A := R, B := P, P := S, from H8
  have s2a : R ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_1 (A := R) (B := P) (P := S) (Q := Q) hH8)
  have s2b : ¬ S ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := R) (B := P) (P := S) (Q := Q) hH8)
  have s2c : ¬ Q ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := R) (B := P) (P := S) (Q := Q) hH8)
  -- 3. mun:off-line-apart A := R, B := S, P := Q, from 1
  have s3a : Q ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := R) (B := S) (P := Q) s1a s1c)
  have s3b : Q ≠ S := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := R) (B := S) (P := Q) s1a s1c)
  -- 4. mun:triangle-off-line P := Q, Q := R, R := S, from 1
  have s4 : LeanBridges.Geometry.Triangle Q R S := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := Q) (Q := R) (R := S) s1a s1c)
  -- 5. axi:supplementary-angles A := S, B := R, C := T, D := Q, from H6, H9, 3
  have s5 : EuclideanGeometry.angle S R Q + EuclideanGeometry.angle Q R T = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := S) (B := R) (C := T) (D := Q) hH6 hH9.1 s3b hH9.2.2.1)
  -- 6. obtain X: axi:plane-separation-crossing A := R, B := P, P := S, from H8, 2
  obtain ⟨X, s6a, ⟨s6b, s6c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := R) (B := P) (P := S) (Q := Q) s2a hH8)
  -- 7. mun:on-line-ends A := R, B := S, from 1
  have s7 : S ∈ LeanBridges.Geometry.line R S := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := R) (B := S) s1a)
  -- 8. mun:segment-off-line A := R, B := S, P := Q, Q := S, from 1, 6, 7
  have s8 : 0 < Complex.im ((X - R) / (S - R)) * Complex.im ((Q - R) / (S - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := R) (B := S) (P := Q) (Q := S) (X := X) s1a s7 s1c (by (have h := s6c; rw [sbtw_comm (x := S) (y := X) (z := Q)] at h; exact h) : Sbtw ℝ Q X S))
  -- 9. mun:same-side-same A := R, B := S, P := X, R := P, from H7, 8
  have s9 : 0 < Complex.im ((X - R) / (S - R)) * Complex.im ((P - R) / (S - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := R) (B := S) (P := X) (Q := Q) (R := P) s8 (by (have h := hH7; rw [mul_comm (Complex.im ((P - R) / (S - R))) (Complex.im ((Q - R) / (S - R)))] at h; exact h) : 0 < Complex.im ((Q - R) / (S - R)) * Complex.im ((P - R) / (S - R))))
  -- 10. mun:off-line-swap, from 2
  have s10 : ¬ P ∈ LeanBridges.Geometry.line R Q := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := P) (Q := Q) (R := R) s2a s2c)
  -- 11. mun:ray-side-transfer, from 3, 6, 9, 10
  have s11 : 0 < Complex.im ((X - R) / (Q - R)) * Complex.im ((P - R) / (Q - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_ray_side_transfer (P := P) (Q := Q) (R := R) (S := S) (X := X) s6b s9 (Ne.symm s3a) s10)
  -- 12. mun:on-line-ends A := R, B := Q, from 3
  have s12 : Q ∈ LeanBridges.Geometry.line R Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := R) (B := Q) (Ne.symm s3a))
  -- 13. mun:off-line-swap P := S, from 1
  have s13 : ¬ S ∈ LeanBridges.Geometry.line R Q := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := S) (Q := Q) (R := R) s1a s1c)
  -- 14. mun:segment-off-line A := R, B := Q, P := S, from 3, 6, 12, 13
  have s14 : 0 < Complex.im ((X - R) / (Q - R)) * Complex.im ((S - R) / (Q - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := R) (B := Q) (P := S) (Q := Q) (X := X) (Ne.symm s3a) s12 s13 s6c)
  -- 15. mun:same-side-same A := R, B := Q, Q := X, R := S, from 11, 14
  have s15 : 0 < Complex.im ((P - R) / (Q - R)) * Complex.im ((S - R) / (Q - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := R) (B := Q) (P := P) (Q := X) (R := S) (by (have h := s11; rw [mul_comm (Complex.im ((X - R) / (Q - R))) (Complex.im ((P - R) / (Q - R)))] at h; exact h) : 0 < Complex.im ((P - R) / (Q - R)) * Complex.im ((X - R) / (Q - R))) s14)
  -- 16. axi:angle-addition-inside A := R, B := S, C := Q, D := P, from H7, 4, 15
  have s16 : EuclideanGeometry.angle S R P + EuclideanGeometry.angle P R Q = EuclideanGeometry.angle S R Q := by exact (Parley.Items.Stdlib.Geometry.axi_angle_addition_inside (A := R) (B := S) (C := Q) (D := P) (by (have h := s4; rw [LeanBridges.Geometry.triangle_rot_231 Q R S] at h; exact h) : LeanBridges.Geometry.Triangle R S Q) hH7 s15)
  -- 17. mun:angle-turned P := T, Q := R, R := Q, from H9
  have s17 : EuclideanGeometry.angle T R Q = EuclideanGeometry.angle Q R T := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := T) (Q := R) (R := Q) (Ne.symm hH9.2.1) hH9.1 (Ne.symm hH9.2.2.1))
  -- 18. algebra, from 5, 16, 17
  linear_combination ((32400) / ((180) * (180))) * s5 + ((180) / ((180))) * s16 + ((180) / ((180))) * s17

end Parley.Stdlib.Geometry.AnglesOnALine
