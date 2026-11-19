module

public import Geometry
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
public import Parley.Stdlib.Geometry.AlternateAnglesConverse
public import Parley.Stdlib.Geometry.VerticalAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.CorrespondingAnglesConverse

theorem corresponding_angles_converse (P : ℂ) (X : ℂ) (Q : ℂ) (Y : ℂ) (R : ℂ) (hH6 : Sbtw ℝ P X Q) (hH7 : 0 < Complex.im ((Y - P) / (Q - P)) * Complex.im ((R - P) / (Q - P))) (hH8 : EuclideanGeometry.angle P X Y = EuclideanGeometry.angle P Q R) (hH9 : X ≠ Y) :
    Complex.im ((Y - X) / (R - Q)) = 0 := by
  -- 1. mun:between-apart R := X, S := P, T := Q, from H6
  have s1a : P ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := X) (S := P) (T := Q) hH6)
  have s1b : Q ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := X) (S := P) (T := Q) hH6)
  -- 2. mun:same-side-off-line A := P, B := Q, P := Y, Q := R, from H7
  have s2a : P ≠ Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_1 (A := P) (B := Q) (P := Y) (Q := R) hH7)
  have s2b : ¬ Y ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := P) (B := Q) (P := Y) (Q := R) hH7)
  have s2c : ¬ R ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := P) (B := Q) (P := Y) (Q := R) hH7)
  -- 3. mun:between-collinear R := X, S := P, T := Q, from H6
  have s3 : Collinear ℝ {Q, X, P} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := X) (S := P) (T := Q) hH6)
  -- 4. def:on-line P := X, A := P, B := Q, from 2, 3
  have s4 : X ∈ LeanBridges.Geometry.line P Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := P) (B := Q) (P := X) s2a)).mpr (by (have h := s3; rw [LeanBridges.Geometry.collinear_rot_312 Q X P] at h; exact h) : Collinear ℝ {P, Q, X})
  -- 5. mun:on-line-ends A := P, B := Q, from 2
  have s5a : P ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := Q) s2a)
  have s5b : Q ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := P) (B := Q) s2a)
  -- 6. mun:on-line-ends A := X, B := Q, from 1
  have s6a : X ∈ LeanBridges.Geometry.line X Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := X) (B := Q) (Ne.symm s1b))
  have s6b : Q ∈ LeanBridges.Geometry.line X Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := X) (B := Q) (Ne.symm s1b))
  -- 7. mun:same-side-of-line A := P, B := Q, C := X, D := Q, P := Y, Q := R, from H7, 1, 2, 4, 5
  have s7 : 0 < Complex.im ((Y - X) / (Q - X)) * Complex.im ((R - X) / (Q - X)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := P) (B := Q) (C := X) (D := Q) (P := Y) (Q := R) s2a (Ne.symm s1b) s4 s5b hH7)
  -- 8. mun:same-side-off-line A := X, B := Q, P := Y, Q := R, from 7
  have s8a : ¬ Y ∈ LeanBridges.Geometry.line X Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := X) (B := Q) (P := Y) (Q := R) s7)
  have s8b : ¬ R ∈ LeanBridges.Geometry.line X Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := X) (B := Q) (P := Y) (Q := R) s7)
  -- 9. mun:triangle-off-line P := Y, Q := P, R := Q, from 2
  have s9 : LeanBridges.Geometry.Triangle Y P Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := Y) (Q := P) (R := Q) s2a s2b)
  -- 10. axi:distance-positive P := Y, Q := X, from H9
  have s10 : dist Y X > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := Y) (Q := X) (Ne.symm hH9))
  -- 11. obtain W: mun:segment-extension A := Y, B := X, r := |YX|, from H9, 10
  obtain ⟨W, s11a, ⟨s11b, s11c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := Y) (B := X) (r := dist Y X) (Ne.symm hH9) s10)
  -- 12. mun:on-off-apart A := P, B := Q, X := Q, Y := R, from 2, 5
  have s12 : Q ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := P) (B := Q) (X := Q) (Y := R) s5b s2c)
  -- 13. mun:segment-across-line A := X, B := Q, P := Y, Q := W, M := X, from 1, 6, 8, 11
  have s13 : Complex.im ((Y - X) / (Q - X)) * Complex.im ((W - X) / (Q - X)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := X) (B := Q) (M := X) (P := Y) (Q := W) (Ne.symm s1b) s6a s8a s11b)
  -- 14. calculation
  have r4215_1 : LeanBridges.Geometry.Triangle Y P X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := Y) (Q := P) (R := Q) (S := X) s9 hH6)
  have r4215_2 : R ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := X) (B := Q) (P := R) (Ne.symm s1b) s8b)
  have r4215_3 : R ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := P) (B := Q) (P := R) s2a s2c)
  have r4215_4 : ¬ W ∈ LeanBridges.Geometry.line X Q := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := X) (B := Q) (P := Y) (Q := W) s13)
  have r4215_5 : LeanBridges.Geometry.Triangle W X Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := W) (Q := X) (R := Q) (Ne.symm s1b) r4215_4)
  have s14 : EuclideanGeometry.angle W X Q = EuclideanGeometry.angle X Q R := by
    calc EuclideanGeometry.angle W X Q = EuclideanGeometry.angle Y X P := by exact (Parley.Stdlib.Geometry.VerticalAngles.vertical_angles (A := Y) (B := P) (C := W) (D := Q) (O := X) s11b hH6 (by (have h := r4215_1; rw [LeanBridges.Geometry.triangle_swap_23 Y P X] at h; exact h) : LeanBridges.Geometry.Triangle Y X P) r4215_5).symm
      _ = EuclideanGeometry.angle P X Y := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := X) (R := Y) r4215_1.2.1 r4215_1.2.2.1 (Ne.symm r4215_1.1)).symm
      _ = EuclideanGeometry.angle P Q R := hH8
      _ = EuclideanGeometry.angle X Q R := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Q) (Q := P) (R := R) (S := X) (by (have h := hH6; rw [sbtw_comm (x := P) (y := X) (z := Q)] at h; exact h) : Sbtw ℝ Q X P) (Ne.symm s12) r4215_2 r4215_3).symm
  -- 15. mun:same-opposite-opposite A := X, B := Q, P := R, Q := Y, R := W, from 7, 13
  have s15 : Complex.im ((R - X) / (Q - X)) * Complex.im ((W - X) / (Q - X)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := X) (B := Q) (P := R) (Q := Y) (R := W) (by (have h := s7; rw [mul_comm (Complex.im ((Y - X) / (Q - X))) (Complex.im ((R - X) / (Q - X)))] at h; exact h) : 0 < Complex.im ((R - X) / (Q - X)) * Complex.im ((Y - X) / (Q - X))) s13)
  -- 16. mun:triangle-off-line P := R, Q := X, R := Q, from 1, 8
  have s16 : LeanBridges.Geometry.Triangle R X Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := R) (Q := X) (R := Q) (Ne.symm s1b) s8b)
  -- 17. thm:alternate-angles-converse P := Q, Q := R, R := X, S := W, from 14, 15, 16
  have s17 : Complex.im ((W - X) / (R - Q)) = 0 := by exact (Parley.Stdlib.Geometry.AlternateAnglesConverse.alternate_angles_converse (P := Q) (Q := R) (R := X) (S := W) (by (have h := s16; rw [LeanBridges.Geometry.triangle_rot_312 R X Q] at h; exact h) : LeanBridges.Geometry.Triangle Q R X) (by (have h := s15; rw [mul_comm (Complex.im ((R - X) / (Q - X))) (Complex.im ((W - X) / (Q - X)))] at h; exact h) : Complex.im ((W - X) / (Q - X)) * Complex.im ((R - X) / (Q - X)) < 0) s14)
  -- 18. mun:between-collinear R := X, S := Y, T := W, from 11
  have s18 : Collinear ℝ {W, X, Y} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := X) (S := Y) (T := W) s11b)
  -- 19. mun:between-apart R := X, S := Y, T := W, from 11
  have s19a : Y ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := X) (S := Y) (T := W) s11b)
  have s19b : W ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := X) (S := Y) (T := W) s11b)
  -- 20. def:on-line P := Y, A := X, B := W, from 18, 19
  have s20 : Y ∈ LeanBridges.Geometry.line X W := ((Parley.Items.Stdlib.Geometry.def_on_line (A := X) (B := W) (P := Y) (Ne.symm s19b))).mpr (by (have h := s18; rw [LeanBridges.Geometry.collinear_swap_12 W X Y] at h; exact h) : Collinear ℝ {X, W, Y})
  -- 21. mun:parallel-along A := X, B := W, C := Q, D := R, E := Y, from 17, 19, 20
  have s21 : Complex.im ((Y - X) / (Q - R)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := X) (B := W) (C := Q) (D := R) (E := Y) s17 (Ne.symm s19b) s20 s19a)
  -- 22. mun:on-line-ends A := X, B := Y, from H9
  have s22 : Y ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := X) (B := Y) hH9)
  -- 23. mun:parallel-along A := X, B := Y, C := R, D := Q, E := Y, from 19, 21, 22
  exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := X) (B := Y) (C := R) (D := Q) (E := Y) s21 (Ne.symm s19a) s22 s19a)

end Parley.Stdlib.Geometry.CorrespondingAnglesConverse
