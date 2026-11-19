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
public import Mathlib.Order.Defs.PartialOrder
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
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.ExteriorAngleGreater

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AlternateAnglesConverse

theorem alternate_angles_converse (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (hH5 : LeanBridges.Geometry.Triangle P Q R) (hH6 : Complex.im ((S - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0) (hH7 : EuclideanGeometry.angle S R P = EuclideanGeometry.angle R P Q) :
    Complex.im ((S - R) / (Q - P)) = 0 := by
  -- 1. mun:opposite-sides-off-line A := R, B := P, P := S, from H6
  have s1a : R ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_1 (A := R) (B := P) (P := S) (Q := Q) hH6)
  have s1b : ¬ S ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := R) (B := P) (P := S) (Q := Q) hH6)
  have s1c : ¬ Q ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := R) (B := P) (P := S) (Q := Q) hH6)
  -- 2. mun:off-line-apart A := R, B := P, P := S, from 1
  have s2a : S ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := R) (B := P) (P := S) s1a s1b)
  have s2b : S ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := R) (B := P) (P := S) s1a s1b)
  -- 3. mun:triangle-not-on-line P := R, Q := P, R := Q, from H5
  have s3 : ¬ R ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := R) (Q := P) (R := Q) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  -- 4. contradiction
  have s4 : ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R S ∧ X ∈ LeanBridges.Geometry.line P Q) := by
    intro hS1
    -- 4.1. restate S1
    have s4_1 : ∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R S ∧ X ∈ LeanBridges.Geometry.line P Q := by exact hS1
    -- 4.2. obtain X from line 4.1
    obtain ⟨X, s4_2a, ⟨s4_2b, s4_2c⟩⟩ := s4_1
    -- 4.3. mun:on-off-apart A := P, B := Q, Y := R, from 3, 4.2
    have s4_3 : X ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := P) (B := Q) (X := X) (Y := R) s4_2c s3)
    -- 4.4. mun:off-line-through, from 1, 4.2, 4.3
    have s4_4 : ¬ X ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_through (P := P) (R := R) (S := S) (X := X) s1b s4_2b s4_3)
    -- 4.5. mun:off-line-apart A := R, B := P, P := X, from 1, 4.4
    have s4_5a : X ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := R) (B := P) (P := X) s1a s4_4)
    have s4_5b : X ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := R) (B := P) (P := X) s1a s4_4)
    -- 4.6. mun:on-line-ends A := R, B := P, from 1
    have s4_6a : R ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := R) (B := P) s1a)
    have s4_6b : P ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := R) (B := P) s1a)
    -- 4.7. axi:plane-separation A := R, B := P, P := X, from 1, 4.4
    have s4_7 : 0 < Complex.im ((X - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) ∨ Complex.im ((X - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.axi_plane_separation (A := R) (B := P) (P := X) (Q := Q) s1a s4_4 s1c)
    -- 4.8. cases, from 4.7
    have s4_8 : EuclideanGeometry.angle S R P ≠ EuclideanGeometry.angle R P Q := by
      rcases s4_7 with hC1 | hC2
      · skip
        -- 4.8.1. mun:same-opposite-opposite A := R, B := P, P := X, R := S, from C1, H6
        have s4_8_1 : Complex.im ((X - R) / (P - R)) * Complex.im ((S - R) / (P - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := R) (B := P) (P := X) (Q := Q) (R := S) hC1 (by (have h := hH6; rw [mul_comm (Complex.im ((S - R) / (P - R))) (Complex.im ((Q - R) / (P - R)))] at h; exact h) : Complex.im ((Q - R) / (P - R)) * Complex.im ((S - R) / (P - R)) < 0))
        -- 4.8.2. mun:line-crossing-between, from 4.2, 4.8.1
        have s4_8_2 : Sbtw ℝ S R X := by exact (Parley.Items.Stdlib.Geometry.mun_line_crossing_between (P := P) (R := R) (S := S) (X := X) s4_2b (by (have h := s4_8_1; rw [mul_comm (Complex.im ((X - R) / (P - R))) (Complex.im ((S - R) / (P - R)))] at h; exact h) : Complex.im ((S - R) / (P - R)) * Complex.im ((X - R) / (P - R)) < 0))
        -- 4.8.3. mun:triangle-off-line P := X, Q := R, R := P, from H5, 4.4
        have s4_8_3 : LeanBridges.Geometry.Triangle X R P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := X) (Q := R) (R := P) (Ne.symm hH5.2.2.1) s4_4)
        -- 4.8.4. thm:exterior-angle-greater A := P, B := X, C := R, D := S, from 4.8.2, 4.8.3
        have r387_1 : LeanBridges.Geometry.Triangle P R S := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := P) (Q := R) (R := X) (S := S) (by (have h := s4_8_3; rw [LeanBridges.Geometry.triangle_swap_13 X R P] at h; exact h) : LeanBridges.Geometry.Triangle P R X) (by (have h := s4_8_2; rw [sbtw_comm (x := S) (y := R) (z := X)] at h; exact h) : Sbtw ℝ X R S))
        have s4_8_4 : EuclideanGeometry.angle P R S > EuclideanGeometry.angle X P R := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreater.exterior_angle_greater (A := P) (B := X) (C := R) (D := S) (by (have h := s4_8_3; rw [LeanBridges.Geometry.triangle_rot_312 X R P] at h; exact h) : LeanBridges.Geometry.Triangle P X R) (by (have h := s4_8_2; rw [sbtw_comm (x := S) (y := R) (z := X)] at h; exact h) : Sbtw ℝ X R S) r387_1)
        -- 4.8.5. mun:same-side-of-line A := R, B := P, C := P, D := R, P := X, from C1, H5, 4.6
        have s4_8_5 : 0 < Complex.im ((X - P) / (R - P)) * Complex.im ((Q - P) / (R - P)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := R) (B := P) (C := P) (D := R) (P := X) (Q := Q) (Ne.symm hH5.2.2.1) hH5.2.2.1 s4_6b s4_6a hC1)
        -- 4.8.6. calculation
        have s4_8_6 : EuclideanGeometry.angle S R P > EuclideanGeometry.angle R P Q := by
          calc EuclideanGeometry.angle S R P = EuclideanGeometry.angle P R S := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := S) (Q := R) (R := P) s2a hH5.2.2.1 s2b)
            _ > EuclideanGeometry.angle X P R := s4_8_4
            _ = EuclideanGeometry.angle R P X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := P) (R := R) s4_5b (Ne.symm hH5.2.2.1) s4_5a)
            _ = EuclideanGeometry.angle R P Q := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := P) (Q := Q) (R := R) (X := X) s4_2c s4_8_5)
        -- 4.8.7. inequalities
        exact ne_of_gt (by linarith only [s4_8_6])
      · skip
        -- 4.8.8. mun:opposite-opposite-same A := R, B := P, P := X, R := S, from C2, H6
        have s4_8_8 : 0 < Complex.im ((X - R) / (P - R)) * Complex.im ((S - R) / (P - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_opposite_same (A := R) (B := P) (P := X) (Q := Q) (R := S) hC2 (by (have h := hH6; rw [mul_comm (Complex.im ((S - R) / (P - R))) (Complex.im ((Q - R) / (P - R)))] at h; exact h) : Complex.im ((Q - R) / (P - R)) * Complex.im ((S - R) / (P - R)) < 0))
        -- 4.8.9. mun:opposite-sides-of-line A := R, B := P, C := P, D := R, P := Q, Q := X, from C2, H5, 4.6
        have s4_8_9 : Complex.im ((Q - P) / (R - P)) * Complex.im ((X - P) / (R - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_of_line (A := R) (B := P) (C := P) (D := R) (P := Q) (Q := X) (Ne.symm hH5.2.2.1) hH5.2.2.1 s4_6b s4_6a (by (have h := hC2; rw [mul_comm (Complex.im ((X - R) / (P - R))) (Complex.im ((Q - R) / (P - R)))] at h; exact h) : Complex.im ((Q - R) / (P - R)) * Complex.im ((X - R) / (P - R)) < 0))
        -- 4.8.10. mun:line-crossing-between R := P, P := R, S := Q, from 4.2, 4.8.9
        have s4_8_10 : Sbtw ℝ Q P X := by exact (Parley.Items.Stdlib.Geometry.mun_line_crossing_between (P := R) (R := P) (S := Q) (X := X) s4_2c s4_8_9)
        -- 4.8.11. mun:triangle-off-line P := X, Q := R, R := P, from H5, 4.4
        have s4_8_11 : LeanBridges.Geometry.Triangle R X P := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := X) (Q := R) (R := P) (Ne.symm hH5.2.2.1) s4_4); rw [LeanBridges.Geometry.triangle_swap_12 X R P] at h; exact h) : LeanBridges.Geometry.Triangle R X P)
        -- 4.8.12. thm:exterior-angle-greater A := R, B := X, C := P, D := Q, from 4.8.10, 4.8.11
        have r426_1 : LeanBridges.Geometry.Triangle R P Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := R) (Q := P) (R := X) (S := Q) (by (have h := s4_8_11; rw [LeanBridges.Geometry.triangle_swap_23 R X P] at h; exact h) : LeanBridges.Geometry.Triangle R P X) (by (have h := s4_8_10; rw [sbtw_comm (x := Q) (y := P) (z := X)] at h; exact h) : Sbtw ℝ X P Q))
        have s4_8_12 : EuclideanGeometry.angle R P Q > EuclideanGeometry.angle X R P := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreater.exterior_angle_greater (A := R) (B := X) (C := P) (D := Q) s4_8_11 (by (have h := s4_8_10; rw [sbtw_comm (x := Q) (y := P) (z := X)] at h; exact h) : Sbtw ℝ X P Q) r426_1)
        -- 4.8.13. calculation
        have s4_8_13 : EuclideanGeometry.angle R P Q > EuclideanGeometry.angle S R P := by
          calc EuclideanGeometry.angle R P Q > EuclideanGeometry.angle X R P := s4_8_12
            _ = EuclideanGeometry.angle P R X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := R) (R := P) s4_5a hH5.2.2.1 s4_5b)
            _ = EuclideanGeometry.angle P R S := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := R) (Q := S) (R := P) (X := X) s4_2b s4_8_8)
            _ = EuclideanGeometry.angle S R P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := R) (R := S) hH5.2.2.1 s2a (Ne.symm s2b))
        -- 4.8.14. inequalities
        exact ne_of_lt (by linarith only [s4_8_13])
    -- 4.9. inequalities, from 4.8
    have s4_9 : EuclideanGeometry.angle S R P ≠ EuclideanGeometry.angle R P Q := s4_8
    exact s4_9 hH7
  -- 5. mun:or-right, from 4
  have s5 : LeanBridges.Geometry.line R S = LeanBridges.Geometry.line P Q ∨ ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R S ∧ X ∈ LeanBridges.Geometry.line P Q) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := LeanBridges.Geometry.line R S = LeanBridges.Geometry.line P Q) (Q := ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R S ∧ X ∈ LeanBridges.Geometry.line P Q)) s4)
  -- 6. def:parallel A := R, B := S, C := P, D := Q, from H5, 2, 5
  exact ((Parley.Items.Stdlib.Geometry.def_parallel (A := R) (B := S) (C := P) (D := Q) (Ne.symm s2a) hH5.1)).mpr s5

end Parley.Stdlib.Geometry.AlternateAnglesConverse
