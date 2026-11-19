module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
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
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.AlternateAnglesConverse

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AlternateAngles

theorem alternate_angles (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (hH5 : LeanBridges.Geometry.Triangle P Q R) (hH6 : Complex.im ((S - R) / (Q - P)) = 0) (hH7 : Complex.im ((S - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0) :
    EuclideanGeometry.angle S R P = EuclideanGeometry.angle R P Q := by
  -- 1. mun:opposite-sides-off-line A := R, B := P, P := S, from H7
  have s1 : ¬ S ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := R) (B := P) (P := S) (Q := Q) hH7)
  -- 2. mun:off-line-apart A := R, B := P, P := S, from H5, 1
  have s2a : S ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := R) (B := P) (P := S) (Ne.symm hH5.2.2.1) s1)
  have s2b : S ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := R) (B := P) (P := S) (Ne.symm hH5.2.2.1) s1)
  -- 3. mun:triangle-off-line P := S, Q := R, R := P, from H5, 1
  have s3 : LeanBridges.Geometry.Triangle S R P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := S) (Q := R) (R := P) (Ne.symm hH5.2.2.1) s1)
  -- 4. axi:angle-measure P := R, Q := P, R := Q, from H5
  have s4a : EuclideanGeometry.angle R P Q > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := R) (Q := P) (R := Q) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  have s4b : EuclideanGeometry.angle R P Q < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := R) (Q := P) (R := Q) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  -- 5. obtain T: axi:angle-construction A := R, B := P, C := S, x := ∠RPQ, from 3, 4
  obtain ⟨T, s5a, ⟨s5b, s5c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_angle_construction (A := R) (B := P) (C := S) (x := EuclideanGeometry.angle R P Q) (by (have h := s3; rw [LeanBridges.Geometry.triangle_rot_231 S R P] at h; exact h) : LeanBridges.Geometry.Triangle R P S) s4a s4b)
  -- 6. mun:same-opposite-opposite A := R, B := P, P := T, Q := S, R := Q, from H7, 5
  have s6 : Complex.im ((T - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := R) (B := P) (P := T) (Q := S) (R := Q) s5b hH7)
  -- 7. mun:opposite-sides-off-line A := R, B := P, P := T, from 6
  have s7 : ¬ T ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := R) (B := P) (P := T) (Q := Q) s6)
  -- 8. mun:off-line-apart A := R, B := P, P := T, from H5, 7
  have s8a : T ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := R) (B := P) (P := T) (Ne.symm hH5.2.2.1) s7)
  have s8b : T ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := R) (B := P) (P := T) (Ne.symm hH5.2.2.1) s7)
  -- 9. calculation
  have s9 : EuclideanGeometry.angle T R P = EuclideanGeometry.angle R P Q := by
    calc EuclideanGeometry.angle T R P = EuclideanGeometry.angle P R T := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := T) (Q := R) (R := P) s8a hH5.2.2.1 s8b)
      _ = EuclideanGeometry.angle R P Q := s5c
  -- 10. thm:alternate-angles-converse S := T, from H5, 6, 9
  have s10 : Complex.im ((T - R) / (Q - P)) = 0 := by exact (Parley.Stdlib.Geometry.AlternateAnglesConverse.alternate_angles_converse (P := P) (Q := Q) (R := R) (S := T) hH5 s6 s9)
  -- 11. mun:triangle-not-on-line P := R, Q := P, R := Q, from H5
  have s11 : ¬ R ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := R) (Q := P) (R := Q) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  -- 12. axi:parallel-uniqueness A := P, B := Q, P := R, C := S, D := T, from H5, H6, 2, 8, 10, 11
  have s12 : LeanBridges.Geometry.line R S = LeanBridges.Geometry.line R T := by exact (Parley.Items.Stdlib.Geometry.axi_parallel_uniqueness (A := P) (B := Q) (C := S) (D := T) (P := R) hH5.1 s11 (Ne.symm s2a) (Ne.symm s8a) hH6 s10)
  -- 13. mun:on-line-ends A := R, B := T, from 8
  have s13 : T ∈ LeanBridges.Geometry.line R T := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := R) (B := T) (Ne.symm s8a))
  -- 14. substitute line RS = line RT (line 12) into line 13
  have s14 : T ∈ LeanBridges.Geometry.line R S := Eq.subst (motive := (fun t : Set ℂ => T ∈ t)) s12.symm s13
  -- 15. calculation
  calc EuclideanGeometry.angle S R P = EuclideanGeometry.angle P R S := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := S) (Q := R) (R := P) s2a hH5.2.2.1 s2b)
    _ = EuclideanGeometry.angle P R T := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := R) (Q := S) (R := P) (X := T) s14 s5b).symm
    _ = EuclideanGeometry.angle R P Q := s5c

end Parley.Stdlib.Geometry.AlternateAngles
