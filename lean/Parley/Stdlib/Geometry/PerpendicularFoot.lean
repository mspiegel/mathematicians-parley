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
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.OffLineAlong
public import Parley.Stdlib.Geometry.RayPoint
public import Parley.Stdlib.Geometry.RightAngleAlong

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.PerpendicularFoot

theorem perpendicular_foot (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    (∃ H ∈ (Set.univ : Set ℂ), ((H ∈ LeanBridges.Geometry.line Q R ∧ P ≠ H) ∧ (H ≠ Q → EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180)) ∧ (H ≠ R → EuclideanGeometry.angle P H R = (90 : ℝ) * Real.pi / 180)) := by
  -- 1. axi:distance-positive, from H4
  have s1 : dist P Q > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P) (Q := Q) hH4.1)
  -- 2. obtain X: mun:segment-extension A := P, B := Q, r := |PQ|, from H4, 1
  obtain ⟨X, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := P) (B := Q) (r := dist P Q) hH4.1 s1)
  -- 3. mun:on-line-ends A := Q, B := R, from H4
  have s3a : Q ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := Q) (B := R) hH4.2.1)
  have s3b : R ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := Q) (B := R) hH4.2.1)
  -- 4. mun:triangle-not-on-line, from H4
  have s4 : ¬ P ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := P) (Q := Q) (R := R) hH4)
  -- 5. mun:segment-across-line A := Q, B := R, Q := X, M := Q, from H4, 2, 3, 4
  have s5 : Complex.im ((P - Q) / (R - Q)) * Complex.im ((X - Q) / (R - Q)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := Q) (B := R) (M := Q) (P := P) (Q := X) hH4.2.1 s3a s4 s2b)
  -- 6. mun:opposite-sides-off-line A := Q, B := R, Q := X, from 5
  have s6a : Q ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_1 (A := Q) (B := R) (P := P) (Q := X) s5)
  have s6b : ¬ P ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := Q) (B := R) (P := P) (Q := X) s5)
  have s6c : ¬ X ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := Q) (B := R) (P := P) (Q := X) s5)
  -- 7. mun:triangle-off-line P := X, from 6
  have s7 : LeanBridges.Geometry.Triangle X Q R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := X) (Q := Q) (R := R) s6a s6c)
  -- 8. axi:angle-measure P := R, R := P, from H4
  have s8a : EuclideanGeometry.angle R Q P > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := R) (Q := Q) (R := P) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R Q P))
  have s8b : EuclideanGeometry.angle R Q P < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := R) (Q := Q) (R := P) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R Q P))
  -- 9. obtain D: axi:angle-construction A := Q, B := R, C := X, x := ∠RQP, from 7, 8
  obtain ⟨D, s9a, s9b⟩ := (Parley.Items.Stdlib.Geometry.axi_angle_construction (A := Q) (B := R) (C := X) (x := EuclideanGeometry.angle R Q P) (by (have h := s7; rw [LeanBridges.Geometry.triangle_rot_231 X Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q R X) s8a s8b)
  -- 10. mun:same-side-off-line A := Q, B := R, P := D, Q := X, from 9
  have s10a : Q ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_1 (A := Q) (B := R) (P := D) (Q := X) s9b.1)
  have s10b : ¬ D ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := Q) (B := R) (P := D) (Q := X) s9b.1)
  have s10c : ¬ X ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := Q) (B := R) (P := D) (Q := X) s9b.1)
  -- 11. mun:triangle-off-line P := D, from 10
  have s11 : LeanBridges.Geometry.Triangle D Q R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := Q) (R := R) s10a s10b)
  -- 12. obtain P′: mun:ray-point A := Q, B := D, C := R, r := |PQ|, from 1, 11
  obtain ⟨P', s12a, s12b⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := Q) (B := D) (C := R) (r := dist P Q) (by (have h := s11; rw [LeanBridges.Geometry.triangle_swap_12 D Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q D R) s1)
  -- 13. mun:angle-same-ray P := Q, Q := D, X := P′, from 12
  have s13 : EuclideanGeometry.angle R Q P' = EuclideanGeometry.angle R Q D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := Q) (Q := D) (R := R) (X := P') s12b.1.1 s12b.1.2)
  -- 14. transitivity, from 13, 9
  have s14 : EuclideanGeometry.angle R Q P' = EuclideanGeometry.angle R Q P := by exact Eq.trans s13 s9b.2
  -- 15. mun:same-side-same A := Q, B := R, P := P′, Q := D, R := X, from 9, 12
  have s15 : 0 < Complex.im ((P' - Q) / (R - Q)) * Complex.im ((X - Q) / (R - Q)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := Q) (B := R) (P := P') (Q := D) (R := X) s12b.1.2 s9b.1)
  -- 16. mun:same-opposite-opposite A := Q, B := R, P := P′, Q := X, R := P, from 5, 15
  have s16 : Complex.im ((P' - Q) / (R - Q)) * Complex.im ((P - Q) / (R - Q)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := Q) (B := R) (P := P') (Q := X) (R := P) s15 (by (have h := s5; rw [mul_comm (Complex.im ((P - Q) / (R - Q))) (Complex.im ((X - Q) / (R - Q)))] at h; exact h) : Complex.im ((X - Q) / (R - Q)) * Complex.im ((P - Q) / (R - Q)) < 0))
  -- 17. obtain H: axi:plane-separation-crossing A := Q, B := R, Q := P′, from H4, 16
  obtain ⟨H, s17a, ⟨s17b, s17c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := Q) (B := R) (P := P) (Q := P') hH4.2.1 (by (have h := s16; rw [mul_comm (Complex.im ((P' - Q) / (R - Q))) (Complex.im ((P - Q) / (R - Q)))] at h; exact h) : Complex.im ((P - Q) / (R - Q)) * Complex.im ((P' - Q) / (R - Q)) < 0))
  -- 18. mun:on-off-apart A := Q, B := R, X := H, Y := P, from 4, 17
  have s18 : P ≠ H := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := Q) (B := R) (X := H) (Y := P) s17b s4)
  -- 19. mun:opposite-sides-off-line A := Q, B := R, Q := P′, from 16
  have s19a : Q ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_1 (A := Q) (B := R) (P := P) (Q := P') (by (have h := s16; rw [mul_comm (Complex.im ((P' - Q) / (R - Q))) (Complex.im ((P - Q) / (R - Q)))] at h; exact h) : Complex.im ((P - Q) / (R - Q)) * Complex.im ((P' - Q) / (R - Q)) < 0))
  have s19b : ¬ P ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := Q) (B := R) (P := P) (Q := P') (by (have h := s16; rw [mul_comm (Complex.im ((P' - Q) / (R - Q))) (Complex.im ((P - Q) / (R - Q)))] at h; exact h) : Complex.im ((P - Q) / (R - Q)) * Complex.im ((P' - Q) / (R - Q)) < 0))
  have s19c : ¬ P' ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := Q) (B := R) (P := P) (Q := P') (by (have h := s16; rw [mul_comm (Complex.im ((P' - Q) / (R - Q))) (Complex.im ((P - Q) / (R - Q)))] at h; exact h) : Complex.im ((P - Q) / (R - Q)) * Complex.im ((P' - Q) / (R - Q)) < 0))
  -- 20. mun:angle-turned, from H4
  have s20 : EuclideanGeometry.angle P Q R = EuclideanGeometry.angle R Q P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := Q) (R := R) hH4.1 (Ne.symm hH4.2.1) hH4.2.2.1)
  -- 21. mun:on-off-apart A := Q, B := R, X := Q, Y := P′, from 3, 19
  have s21 : Q ≠ P' := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := Q) (B := R) (X := Q) (Y := P') s3a s19c)
  -- 22. mun:on-off-apart A := Q, B := R, X := R, Y := P′, from 3, 19
  have s22 : R ≠ P' := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := Q) (B := R) (X := R) (Y := P') s3b s19c)
  -- 23. mun:on-off-apart A := Q, B := R, X := H, Y := P′, from 17, 19
  have s23 : H ≠ P' := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := Q) (B := R) (X := H) (Y := P') s17b s19c)
  -- 24. mun:angle-turned P := P′, from H4, 21, 22
  have s24 : EuclideanGeometry.angle P' Q R = EuclideanGeometry.angle R Q P' := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P') (Q := Q) (R := R) (Ne.symm s21) (Ne.symm hH4.2.1) (Ne.symm s22))
  -- 25. restate 17
  have s25 : Sbtw ℝ P H P' := by exact s17c
  -- 26. proof
  have s26 : H ≠ Q → EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by
    intro hK1
    -- 26.1. mun:on-line-cases P := H, from H4, 17
    have s26_1 : (((H = Q ∨ Sbtw ℝ Q H R) ∨ H = R) ∨ Sbtw ℝ Q R H) ∨ Sbtw ℝ H Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := H) (Q := Q) (R := R) hH4.2.1 s17b)
    -- 26.2. cases, from 26.1
    have s26_2 : EuclideanGeometry.angle H Q P = EuclideanGeometry.angle H Q P' := by
      rcases s26_1 with (((hC1 | hC2) | hC3) | hC4) | hC5
      · skip
        -- 26.2.1. restate K1
        have s26_2_1 : H ≠ Q := by exact hK1
        exact absurd hC1 s26_2_1
      · skip
        -- 26.2.2. mun:angle-along-segment P := Q, Q := R, S := H, R := P, from C2, H4, 18
        have s26_2_2 : EuclideanGeometry.angle H Q P = EuclideanGeometry.angle R Q P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Q) (Q := R) (R := P) (S := H) hC2 hH4.1 s18 hH4.2.2.1)
        -- 26.2.3. mun:angle-along-segment P := Q, Q := R, S := H, R := P′, from C2, 21, 22, 23
        have s26_2_3 : EuclideanGeometry.angle H Q P' = EuclideanGeometry.angle R Q P' := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Q) (Q := R) (R := P') (S := H) hC2 (Ne.symm s21) (Ne.symm s23) (Ne.symm s22))
        -- 26.2.4. calculation
        calc EuclideanGeometry.angle H Q P = EuclideanGeometry.angle R Q P := s26_2_2
          _ = EuclideanGeometry.angle R Q P' := s14.symm
          _ = EuclideanGeometry.angle H Q P' := s26_2_3.symm
      · skip
        -- 26.2.5. substitute H = R (C3) into line 14
        have s26_2_5 : EuclideanGeometry.angle H Q P' = EuclideanGeometry.angle H Q P := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle t Q P' = EuclideanGeometry.angle t Q P)) hC3.symm s14
        -- 26.2.6. restate 26.2.5
        exact s26_2_5.symm
      · skip
        -- 26.2.7. mun:angle-along-segment P := Q, Q := H, S := R, R := P, from C4, H4, 18
        have s26_2_7 : EuclideanGeometry.angle R Q P = EuclideanGeometry.angle H Q P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Q) (Q := H) (R := P) (S := R) hC4 hH4.1 hH4.2.2.1 s18)
        -- 26.2.8. mun:angle-along-segment P := Q, Q := H, S := R, R := P′, from C4, 21, 22, 23
        have s26_2_8 : EuclideanGeometry.angle R Q P' = EuclideanGeometry.angle H Q P' := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Q) (Q := H) (R := P') (S := R) hC4 (Ne.symm s21) (Ne.symm s22) (Ne.symm s23))
        -- 26.2.9. calculation
        calc EuclideanGeometry.angle H Q P = EuclideanGeometry.angle R Q P := s26_2_7.symm
          _ = EuclideanGeometry.angle R Q P' := s14.symm
          _ = EuclideanGeometry.angle H Q P' := s26_2_8
      · skip
        -- 26.2.10. axi:supplementary-angles A := H, B := Q, C := R, D := P, from C5, H4, 18
        have s26_2_10 : EuclideanGeometry.angle H Q P + EuclideanGeometry.angle P Q R = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := H) (B := Q) (C := R) (D := P) hC5 hH4.1 s18 hH4.2.2.1)
        -- 26.2.11. axi:supplementary-angles A := H, B := Q, C := R, D := P′, from C5, 21, 22, 23
        have s26_2_11 : EuclideanGeometry.angle H Q P' + EuclideanGeometry.angle P' Q R = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := H) (B := Q) (C := R) (D := P') hC5 (Ne.symm s21) (Ne.symm s23) (Ne.symm s22))
        -- 26.2.12. algebra, from 14, 20, 24, 26.2.10, 26.2.11
        linear_combination s14 + (-1) * s20 + s24 + ((180) / ((180))) * s26_2_10 + ((-180) / ((180))) * s26_2_11
    -- 26.3. calculation
    have s26_3 : EuclideanGeometry.angle P Q H = EuclideanGeometry.angle P' Q H := by
      calc EuclideanGeometry.angle P Q H = EuclideanGeometry.angle H Q P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := Q) (R := H) hH4.1 hK1 s18)
        _ = EuclideanGeometry.angle H Q P' := s26_2
        _ = EuclideanGeometry.angle P' Q H := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P') (Q := Q) (R := H) (Ne.symm s21) hK1 (Ne.symm s23)).symm
    -- 26.4. mun:off-line-along A := Q, B := R, X := H, from H4, K1, 4, 17
    have s26_4 : ¬ P ∈ LeanBridges.Geometry.line Q H := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := Q) (B := R) (X := H) (P := P) hH4.2.1 s17b hK1 s4)
    -- 26.5. mun:off-line-along A := Q, B := R, X := H, P := P′, from K1, 17, 19
    have s26_5 : ¬ P' ∈ LeanBridges.Geometry.line Q H := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := Q) (B := R) (X := H) (P := P') s19a s17b hK1 s19c)
    -- 26.6. mun:triangle-off-line R := H, from K1, 26.4
    have s26_6 : LeanBridges.Geometry.Triangle P Q H := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := P) (Q := Q) (R := H) (Ne.symm hK1) s26_4)
    -- 26.7. mun:triangle-off-line P := P′, R := H, from K1, 26.5
    have s26_7 : LeanBridges.Geometry.Triangle P' Q H := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := P') (Q := Q) (R := H) (Ne.symm hK1) s26_5)
    -- 26.8. axi:side-angle-side R := H, Q′ := Q, R′ := H, from 12, 26.3, 26.6, 26.7
    have s26_8 : dist P Q = dist P' Q ∧ dist Q H = dist Q H ∧ dist H P = dist H P' ∧ EuclideanGeometry.angle P Q H = EuclideanGeometry.angle P' Q H ∧ EuclideanGeometry.angle Q H P = EuclideanGeometry.angle Q H P' ∧ EuclideanGeometry.angle H P Q = EuclideanGeometry.angle H P' Q := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := P) (P' := P') (Q := Q) (Q' := Q) (R := H) (R' := H) s26_6 s26_7 (by (have h := s12b.2.symm; rw [dist_comm Q P'] at h; exact h) : dist P Q = dist P' Q) s26_3 rfl)
    -- 26.9. def:congruent R := H, Q′ := Q, R′ := H, from 26.6, 26.7, 26.8
    have s26_9 : ((((dist P Q = dist P' Q ∧ dist Q H = dist Q H) ∧ dist H P = dist H P') ∧ EuclideanGeometry.angle P Q H = EuclideanGeometry.angle P' Q H) ∧ EuclideanGeometry.angle Q H P = EuclideanGeometry.angle Q H P') ∧ EuclideanGeometry.angle H P Q = EuclideanGeometry.angle H P' Q := by exact ((Parley.Items.Stdlib.Geometry.def_congruent (P := P) (P' := P') (Q := Q) (Q' := Q) (R := H) (R' := H) s26_6 s26_7)).mp s26_8
    -- 26.10. axi:supplementary-angles A := P, B := H, C := P′, D := Q, from H4, K1, 21, 25
    have s26_10 : EuclideanGeometry.angle P H Q + EuclideanGeometry.angle Q H P' = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := P) (B := H) (C := P') (D := Q) s25 (Ne.symm hK1) (Ne.symm hH4.1) s21)
    -- 26.11. mun:angle-turned Q := H, R := Q, from H4, K1, 18
    have s26_11 : EuclideanGeometry.angle P H Q = EuclideanGeometry.angle Q H P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := H) (R := Q) s18 (Ne.symm hK1) hH4.1)
    -- 26.12. algebra, from 26.9, 26.10, 26.11
    linear_combination ((90) / ((180))) * s26_9.1.2 + ((16200) / ((180) * (180))) * s26_10 + ((90) / ((180))) * s26_11
  -- 27. proof
  have s27 : H ≠ R → EuclideanGeometry.angle P H R = (90 : ℝ) * Real.pi / 180 := by
    intro hK2
    -- 27.1. axi:excluded-middle P := H = Q
    have s27_1 : H = Q ∨ H ≠ Q := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := H = Q))
    -- 27.2. cases, from 27.1
    rcases s27_1 with hC6 | hC7
    · skip
      -- 27.2.1. substitute H = Q (C6) into line 25
      have s27_2_1 : Sbtw ℝ P Q P' := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ P t P')) hC6 s25
      -- 27.2.2. axi:supplementary-angles A := P, B := Q, C := P′, D := R, from H4, 22, 27.2.1
      have s27_2_2 : EuclideanGeometry.angle P Q R + EuclideanGeometry.angle R Q P' = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := P) (B := Q) (C := P') (D := R) s27_2_1 (Ne.symm hH4.2.1) (Ne.symm hH4.2.2.1) s22)
      -- 27.2.3. algebra, from 14, 20, 27.2.2
      have s27_2_3 : EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180 := by linear_combination ((-90) / ((180))) * s14 + ((90) / ((180))) * s20 + ((16200) / ((180) * (180))) * s27_2_2
      -- 27.2.4. substitute H = Q (C6) into line 27.2.3
      exact Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle P t R = (90 : ℝ) * Real.pi / 180)) hC6.symm s27_2_3
    · skip
      -- 27.2.5. mun:modus-ponens, from C7, 26
      have s27_2_5 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ Q) (Q := EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) s26 hC7)
      -- 27.2.6. axi:line-uniqueness A := H, B := Q, C := Q, D := R, from C7, H4, 3, 17
      have s27_2_6 : LeanBridges.Geometry.line H Q = LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := H) (B := Q) (C := Q) (D := R) hC7 hH4.2.1 s17b s3a)
      -- 27.2.7. substitute line HQ = line QR (line 27.2.6) into line 3
      have s27_2_7 : R ∈ LeanBridges.Geometry.line H Q := Eq.subst (motive := (fun t : Set ℂ => R ∈ t)) s27_2_6.symm s3b
      -- 27.2.8. mun:right-angle-along S := Q, T := R, from 27.2.5, 27.2.7
      have r1416_1 : LeanBridges.Geometry.Triangle P H Q := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := P) (Q := H) (R := Q) s18 (Ne.symm hC7) s27_2_5 hH4.1)
      have r1416_2 : ¬ P ∈ LeanBridges.Geometry.line H Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := P) (Q := H) (R := Q) r1416_1)
      have r1416_3 : ¬ P ∈ LeanBridges.Geometry.line H R := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := H) (B := Q) (X := R) (P := P) hC7 s27_2_7 (Ne.symm hK2) r1416_2)
      have r1416_4 : LeanBridges.Geometry.Triangle P H R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := P) (Q := H) (R := R) hK2 r1416_3)
      exact (Parley.Stdlib.Geometry.RightAngleAlong.right_angle_along (P := P) (H := H) (S := Q) (T := R) r1416_1.1 (Ne.symm r1416_1.2.1) s27_2_5 s27_2_7 (Ne.symm r1416_4.2.1) r1416_1.2.2.1 r1416_4)
  -- 28. exhibit, from 17, 18, 26, 27
  exact ⟨H, Set.mem_univ _, ⟨⟨⟨s17b, s18⟩, s26⟩, s27⟩⟩

end Parley.Stdlib.Geometry.PerpendicularFoot
