module

public import Geometry
public import Batteries.Tactic.Init
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
public import Parley.Stdlib.Geometry.CorrespondingAnglesConverse
public import Parley.Stdlib.Geometry.OffLineAlong
public import Parley.Stdlib.Geometry.ParallelBetween
public import Parley.Stdlib.Geometry.ProportionalSegments
public import Parley.Stdlib.Geometry.RayPoint

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AngleAngleSimilar

theorem angle_angle_similar (P : ℂ) (Q : ℂ) (R : ℂ) (P' : ℂ) (Q' : ℂ) (R' : ℂ) (hH7 : LeanBridges.Geometry.Triangle P Q R) (hH8 : LeanBridges.Geometry.Triangle P' Q' R') (hH9 : EuclideanGeometry.angle Q P R = EuclideanGeometry.angle Q' P' R') (hH10 : EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R') :
    dist P Q * dist P' R' = dist P' Q' * dist P R := by
  -- 1. axi:distance-positive P := P′, Q := Q′, from H8
  have s1 : dist P' Q' > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P') (Q := Q') hH8.1)
  -- 2. axi:distance-positive P := P′, Q := R′, from H8
  have s2 : dist P' R' > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P') (Q := R') hH8.2.2.1)
  -- 3. obtain X: mun:ray-point A := P, B := Q, C := R, r := |P′Q′|, from H7, 1
  obtain ⟨X, s3a, ⟨⟨s3b, s3c⟩, s3d⟩⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := P) (B := Q) (C := R) (r := dist P' Q') hH7 s1)
  -- 4. obtain Y: mun:ray-point A := P, B := R, C := Q, r := |P′R′|, from H7, 2
  obtain ⟨Y, s4a, ⟨⟨s4b, s4c⟩, s4d⟩⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := P) (B := R) (C := Q) (r := dist P' R') (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_23 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle P R Q) s2)
  -- 5. mun:same-side-off-line A := P, B := R, P := X, from 3
  have s5 : ¬ X ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := P) (B := R) (P := X) (Q := Q) s3c)
  -- 6. mun:off-line-apart A := P, B := R, P := X, from H7, 5
  have s6a : X ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := P) (B := R) (P := X) hH7.2.2.1 s5)
  have s6b : X ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := P) (B := R) (P := X) hH7.2.2.1 s5)
  -- 7. mun:on-line-ends A := P, B := Q, from H7
  have s7a : P ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := Q) hH7.1)
  have s7b : Q ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := P) (B := Q) hH7.1)
  -- 8. mun:same-side-of-line A := P, B := Q, C := P, D := X, P := Y, Q := R, from H7, 3, 4, 6, 7
  have s8 : 0 < Complex.im ((Y - P) / (X - P)) * Complex.im ((R - P) / (X - P)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := P) (B := Q) (C := P) (D := X) (P := Y) (Q := R) hH7.1 (Ne.symm s6a) s7a s3b s4c)
  -- 9. calculation
  have s9 : EuclideanGeometry.angle X P Y = EuclideanGeometry.angle Q P R := by
    calc EuclideanGeometry.angle X P Y = EuclideanGeometry.angle X P R := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := P) (Q := R) (R := X) (X := Y) s4b s8)
      _ = EuclideanGeometry.angle R P X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := P) (R := R) s6a (Ne.symm hH7.2.2.1) s6b)
      _ = EuclideanGeometry.angle R P Q := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := P) (Q := Q) (R := R) (X := X) s3b s3c)
      _ = EuclideanGeometry.angle Q P R := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := R) (Q := P) (R := Q) (Ne.symm hH7.2.2.1) (Ne.symm hH7.1) (Ne.symm hH7.2.1))
  -- 10. mun:same-side-off-line A := P, B := Q, P := Y, Q := R, from 4
  have s10 : ¬ Y ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := P) (B := Q) (P := Y) (Q := R) s4c)
  -- 11. mun:off-line-apart A := P, B := Q, P := Y, from H7, 10
  have s11a : Y ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := P) (B := Q) (P := Y) hH7.1 s10)
  have s11b : Y ≠ Q := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := P) (B := Q) (P := Y) hH7.1 s10)
  -- 12. mun:off-line-along A := P, B := R, X := Y, P := X, from H7, 4, 5, 11
  have s12 : ¬ X ∈ LeanBridges.Geometry.line P Y := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := P) (B := R) (X := Y) (P := X) hH7.2.2.1 s4b s11a s5)
  -- 13. mun:triangle-off-line P := X, Q := P, R := Y, from 11, 12
  have s13 : LeanBridges.Geometry.Triangle X P Y := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := X) (Q := P) (R := Y) (Ne.symm s11a) s12)
  -- 14. calculation
  have s14 : EuclideanGeometry.angle Q' P' R' = EuclideanGeometry.angle X P Y := by
    calc EuclideanGeometry.angle Q' P' R' = EuclideanGeometry.angle Q P R := hH9.symm
      _ = EuclideanGeometry.angle X P Y := s9.symm
  -- 15. restate 3
  have s15 : dist P X = dist P' Q' := by exact s3d
  -- 16. restate 4
  have s16 : dist P Y = dist P' R' := by exact s4d
  -- 17. restate 15
  have s17 : dist Q' P' = dist X P := by exact (by (have h := s15.symm; rw [dist_comm P' Q', dist_comm P X] at h; exact h) : dist Q' P' = dist X P)
  -- 18. restate 16
  have s18 : dist P' R' = dist P Y := by exact s16.symm
  -- 19. axi:side-angle-side P := Q′, Q := P′, R := R′, P′ := X, Q′ := P, R′ := Y, from H8, 13, 14, 17, 18
  have s19 : dist Q' P' = dist X P ∧ dist P' R' = dist P Y ∧ dist R' Q' = dist Y X ∧ EuclideanGeometry.angle Q' P' R' = EuclideanGeometry.angle X P Y ∧ EuclideanGeometry.angle P' R' Q' = EuclideanGeometry.angle P Y X ∧ EuclideanGeometry.angle R' Q' P' = EuclideanGeometry.angle Y X P := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := Q') (P' := X) (Q := P') (Q' := P) (R := R') (R' := Y) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 P' Q' R'] at h; exact h) : LeanBridges.Geometry.Triangle Q' P' R') s13 s17 s14 s18)
  -- 20. calculation
  have s20 : EuclideanGeometry.angle P X Y = EuclideanGeometry.angle P Q R := by
    calc EuclideanGeometry.angle P X Y = EuclideanGeometry.angle Y X P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := X) (R := Y) (Ne.symm s13.1) (Ne.symm s13.2.2.1) s13.2.1)
      _ = EuclideanGeometry.angle R' Q' P' := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := Q') (P' := X) (Q := P') (Q' := P) (R := R') (R' := Y) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 P' Q' R'] at h; exact h) : LeanBridges.Geometry.Triangle Q' P' R') s13)).mp s19).2.symm
      _ = EuclideanGeometry.angle P' Q' R' := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := R') (Q := Q') (R := P') (Ne.symm hH8.2.1) hH8.1 (Ne.symm hH8.2.2.1))
      _ = EuclideanGeometry.angle P Q R := hH10.symm
  -- 21. mun:on-line-cases P := X, Q := P, R := Q, from H7, 3
  have s21 : (((X = P ∨ Sbtw ℝ P X Q) ∨ X = Q) ∨ Sbtw ℝ P Q X) ∨ Sbtw ℝ X P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := X) (Q := P) (R := Q) hH7.1 s3b)
  -- 22. cases, from 21
  rcases s21 with (((hC1 | hC2) | hC3) | hC4) | hC5
  · skip
    -- 22.1. def:triangle P := X, Q := P, R := Y, from 13
    have s22_1 : X ≠ P := by exact (((Parley.Items.Stdlib.Geometry.def_triangle (P := X) (Q := P) (R := Y))).mp s13).1.1.1
    exact absurd hC1 s22_1
  · skip
    -- 22.2. thm:corresponding-angles-converse, from C2, 4, 13, 20
    have s22_2 : Complex.im ((Y - X) / (R - Q)) = 0 := by exact (Parley.Stdlib.Geometry.CorrespondingAnglesConverse.corresponding_angles_converse (P := P) (X := X) (Q := Q) (Y := Y) (R := R) hC2 s4c s20 s13.2.2.1)
    -- 22.3. thm:parallel-between, from C2, H7, 4, 22.2
    have s22_3 : Sbtw ℝ P Y R := by exact (Parley.Stdlib.Geometry.ParallelBetween.parallel_between (P := P) (Q := Q) (R := R) (X := X) (Y := Y) hH7 hC2 s4b s4c s22_2)
    -- 22.4. thm:proportional-segments, from C2, H7, 22.2, 22.3
    have s22_4 : dist P X * dist P R = dist P Y * dist P Q := by exact (Parley.Stdlib.Geometry.ProportionalSegments.proportional_segments (P := P) (Q := Q) (R := R) (X := X) (Y := Y) hH7 hC2 s22_3 s22_2)
    -- 22.5. substitute
    have s22_5 : dist P' Q' * dist P R = dist P' R' * dist P Q := by
      have c1 : dist P X = dist P' Q' := congrArg (fun t : ℝ => t) s15
      have row1 : dist P' Q' * dist P R = dist P Y * dist P Q := Eq.subst (motive := (fun t : ℝ => t * dist P R = dist P Y * dist P Q)) c1 s22_4
      have c2 : dist P Y = dist P' R' := congrArg (fun t : ℝ => t) s16
      have row2 : dist P' Q' * dist P R = dist P' R' * dist P Q := Eq.subst (motive := (fun t : ℝ => dist P' Q' * dist P R = t * dist P Q)) c2 row1
      exact row2
    -- 22.6. algebra, from 22.5
    linear_combination (-1) * s22_5
  · skip
    -- 22.7. substitute X = Q (C3) into line 20
    have s22_7 : EuclideanGeometry.angle P Q Y = EuclideanGeometry.angle P Q R := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle P t Y = EuclideanGeometry.angle P Q R)) hC3 s20
    -- 22.8. mun:same-side-of-line A := P, B := Q, C := Q, D := P, P := Y, Q := R, from H7, 4, 7
    have s22_8 : 0 < Complex.im ((Y - Q) / (P - Q)) * Complex.im ((R - Q) / (P - Q)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := P) (B := Q) (C := Q) (D := P) (P := Y) (Q := R) hH7.1 (Ne.symm hH7.1) s7b s7a s4c)
    -- 22.9. mun:same-side-same A := Q, B := P, P := R, Q := Y, from 22.8
    have s22_9 : 0 < Complex.im ((R - Q) / (P - Q)) * Complex.im ((R - Q) / (P - Q)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := Q) (B := P) (P := R) (Q := Y) (R := R) (by (have h := s22_8; rw [mul_comm (Complex.im ((Y - Q) / (P - Q))) (Complex.im ((R - Q) / (P - Q)))] at h; exact h) : 0 < Complex.im ((R - Q) / (P - Q)) * Complex.im ((Y - Q) / (P - Q))) s22_8)
    -- 22.10. axi:angle-construction-unique A := Q, B := P, C := R, D := R, E := Y, from H7, 22.7, 22.8, 22.9
    have s22_10 : Y ∈ LeanBridges.Geometry.ray Q R := by exact (Parley.Items.Stdlib.Geometry.axi_angle_construction_unique (E := Y) (A := Q) (B := P) (C := R) (D := R) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_12 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q P R) s22_9 s22_8 s22_7.symm)
    -- 22.11. mun:ray-on-line P := Y, A := Q, B := R, from 22.10
    have s22_11 : Y ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_ray_on_line (P := Y) (A := Q) (B := R) s22_10)
    -- 22.12. contradiction
    have s22_12 : Y = R := by
      by_contra (hS1 : Y ≠ R)
      -- 22.12.1. mun:on-line-ends A := P, B := R, from H7
      have s22_12_1 : R ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := P) (B := R) hH7.2.2.1)
      -- 22.12.2. axi:line-uniqueness A := Y, B := R, C := P, D := R, from H7, S1, 4, 22.12.1
      have s22_12_2 : LeanBridges.Geometry.line Y R = LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := Y) (B := R) (C := P) (D := R) hS1 hH7.2.2.1 s4b s22_12_1)
      -- 22.12.3. mun:on-line-ends A := Q, B := R, from H7
      have s22_12_3 : R ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := Q) (B := R) hH7.2.1)
      -- 22.12.4. axi:line-uniqueness A := Y, B := R, C := Q, D := R, from H7, S1, 22.11, 22.12.3
      have s22_12_4 : LeanBridges.Geometry.line Y R = LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := Y) (B := R) (C := Q) (D := R) hS1 hH7.2.1 s22_11 s22_12_3)
      -- 22.12.5. calculation
      have s22_12_5 : LeanBridges.Geometry.line P R = LeanBridges.Geometry.line Q R := by
        calc LeanBridges.Geometry.line P R = LeanBridges.Geometry.line Y R := s22_12_2.symm
          _ = LeanBridges.Geometry.line Q R := s22_12_4
      -- 22.12.6. mun:on-line-ends A := P, B := R, from H7
      have s22_12_6 : P ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := R) hH7.2.2.1)
      -- 22.12.7. substitute line PR = line QR (line 22.12.5) into line 22.12.6
      have s22_12_7 : P ∈ LeanBridges.Geometry.line Q R := Eq.subst (motive := (fun t : Set ℂ => P ∈ t)) s22_12_5 s22_12_6
      -- 22.12.8. mun:triangle-not-on-line, from H7
      have s22_12_8 : ¬ P ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := P) (Q := Q) (R := R) hH7)
      exact s22_12_8 s22_12_7
    -- 22.13. substitute X = Q (C3) into line 15
    have s22_13 : dist P Q = dist P' Q' := Eq.subst (motive := (fun t : ℂ => dist P t = dist P' Q')) hC3 s15
    -- 22.14. substitute Y = R (line 22.12) into line 16
    have s22_14 : dist P R = dist P' R' := Eq.subst (motive := (fun t : ℂ => dist P t = dist P' R')) s22_12 s16
    -- 22.15. algebra, from 22.13
    have s22_15 : dist P Q * dist P' R' = dist P' Q' * dist P' R' := by linear_combination (dist P' R') * s22_13
    -- 22.16. algebra, from 22.14
    have s22_16 : dist P' Q' * dist P R = dist P' Q' * dist P' R' := by linear_combination (dist P' Q') * s22_14
    -- 22.17. transitivity, from 22.15, 22.16
    exact Eq.trans s22_15 s22_16.symm
  · skip
    -- 22.18. mun:same-side-of-line A := P, B := Q, C := P, D := X, P := R, Q := Y, from H7, 3, 4, 6, 7
    have s22_18 : 0 < Complex.im ((R - P) / (X - P)) * Complex.im ((Y - P) / (X - P)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := P) (B := Q) (C := P) (D := X) (P := R) (Q := Y) hH7.1 (Ne.symm s6a) s7a s3b (by (have h := s4c; rw [mul_comm (Complex.im ((Y - P) / (Q - P))) (Complex.im ((R - P) / (Q - P)))] at h; exact h) : 0 < Complex.im ((R - P) / (Q - P)) * Complex.im ((Y - P) / (Q - P))))
    -- 22.19. calculation
    have s22_19 : EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P X Y := s20.symm
    -- 22.20. thm:corresponding-angles-converse X := Q, Q := X, Y := R, R := Y, from C4, H7, 22.18, 22.19
    have s22_20 : Complex.im ((R - Q) / (Y - X)) = 0 := by exact (Parley.Stdlib.Geometry.CorrespondingAnglesConverse.corresponding_angles_converse (P := P) (X := Q) (Q := X) (Y := R) (R := Y) hC4 s22_18 s22_19 hH7.2.1)
    -- 22.21. mun:on-line-ends A := P, B := R, from H7
    have s22_21 : R ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := P) (B := R) hH7.2.2.1)
    -- 22.22. mun:on-line-ends A := P, B := R, from H7
    have s22_22 : P ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := R) hH7.2.2.1)
    -- 22.23. axi:line-uniqueness A := P, B := Y, C := P, D := R, from H7, 4, 13, 22.22
    have s22_23 : LeanBridges.Geometry.line P Y = LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := P) (B := Y) (C := P) (D := R) s13.2.1 hH7.2.2.1 s22_22 s4b)
    -- 22.24. substitute line PY = line PR (line 22.23) into line 22.21
    have s22_24 : R ∈ LeanBridges.Geometry.line P Y := Eq.subst (motive := (fun t : Set ℂ => R ∈ t)) s22_23.symm s22_21
    -- 22.25. restate 22.18
    have s22_25 : 0 < Complex.im ((R - P) / (X - P)) * Complex.im ((Y - P) / (X - P)) := by exact s22_18
    -- 22.26. thm:parallel-between Q := X, R := Y, X := Q, Y := R, from C4, 13, 22.20, 22.24, 22.25
    have s22_26 : Sbtw ℝ P R Y := by exact (Parley.Stdlib.Geometry.ParallelBetween.parallel_between (P := P) (Q := X) (R := Y) (X := Q) (Y := R) (by (have h := s13; rw [LeanBridges.Geometry.triangle_swap_12 X P Y] at h; exact h) : LeanBridges.Geometry.Triangle P X Y) hC4 s22_24 s22_25 s22_20)
    -- 22.27. thm:proportional-segments Q := X, R := Y, X := Q, Y := R, from C4, 13, 22.20, 22.26
    have s22_27 : dist P Q * dist P Y = dist P R * dist P X := by exact (Parley.Stdlib.Geometry.ProportionalSegments.proportional_segments (P := P) (Q := X) (R := Y) (X := Q) (Y := R) (by (have h := s13; rw [LeanBridges.Geometry.triangle_swap_12 X P Y] at h; exact h) : LeanBridges.Geometry.Triangle P X Y) hC4 s22_26 s22_20)
    -- 22.28. substitute
    have s22_28 : dist P Q * dist P' R' = dist P R * dist P' Q' := by
      have c1 : dist P Y = dist P' R' := congrArg (fun t : ℝ => t) s16
      have row1 : dist P Q * dist P' R' = dist P R * dist P X := Eq.subst (motive := (fun t : ℝ => dist P Q * t = dist P R * dist P X)) c1 s22_27
      have c2 : dist P X = dist P' Q' := congrArg (fun t : ℝ => t) s15
      have row2 : dist P Q * dist P' R' = dist P R * dist P' Q' := Eq.subst (motive := (fun t : ℝ => dist P Q * dist P' R' = dist P R * t)) c2 row1
      exact row2
    -- 22.29. algebra, from 22.28
    linear_combination s22_28
  · skip
    -- 22.30. mun:on-line-ends A := P, B := R, from H7
    have s22_30 : P ∈ LeanBridges.Geometry.line P R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := R) hH7.2.2.1)
    -- 22.31. mun:segment-across-line A := P, B := R, P := X, M := P, from C5, H7, 5, 22.30
    have s22_31 : Complex.im ((X - P) / (R - P)) * Complex.im ((Q - P) / (R - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := P) (B := R) (M := P) (P := X) (Q := Q) hH7.2.2.1 s22_30 s5 hC5)
    -- 22.32. mun:same-not-opposite A := P, B := R, P := X, from 3
    have s22_32 : ¬ Complex.im ((X - P) / (R - P)) * Complex.im ((Q - P) / (R - P)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := P) (B := R) (P := X) (Q := Q) s3c)
    exact absurd s22_31 s22_32

end Parley.Stdlib.Geometry.AngleAngleSimilar
