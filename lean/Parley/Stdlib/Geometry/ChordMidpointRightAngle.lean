module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.SideSideSide

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ChordMidpointRightAngle

theorem chord_midpoint_right_angle (A : ℂ) (B : ℂ) (M : ℂ) (O : ℂ) (hH5 : Sbtw ℝ A M B ∧ dist A M = dist M B) (hH6 : dist A O = dist B O) (hH7 : O ≠ M) (hH8 : M ≠ B) (hH9 : O ≠ B) :
    EuclideanGeometry.angle O M B = (90 : ℝ) * Real.pi / 180 := by
  -- 1. def:midpoint, from H5
  have s1a : Sbtw ℝ A M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH5).1
  have s1b : dist A M = dist M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH5).2
  -- 2. mun:between-ends-apart R := M, S := A, T := B, from 1
  have s2 : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := M) (S := A) (T := B) s1a)
  -- 3. mun:between-apart R := M, S := A, T := B, from 1
  have s3a : A ≠ M := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := M) (S := A) (T := B) s1a)
  have s3b : B ≠ M := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := M) (S := A) (T := B) s1a)
  -- 4. contradiction
  have s4 : ¬ O ∈ LeanBridges.Geometry.line A B := by
    intro hS
    -- 4.1. mun:on-line-cases P := O, Q := A, R := B, from S, 2
    have s4_1 : (((O = A ∨ Sbtw ℝ A O B) ∨ O = B) ∨ Sbtw ℝ A B O) ∨ Sbtw ℝ O A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := O) (Q := A) (R := B) s2 hS)
    -- 4.2. cases, from 4.1
    have s4_2 : A = B := by
      rcases s4_1 with (((hC1 | hC2) | hC3) | hC4) | hC5
      · skip
        -- 4.2.1. mun:distance-zero P := O, Q := A, from C1
        have s4_2_1 : dist O A = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := O) (Q := A))).mpr hC1
        -- 4.2.2. transitivity, from H6, 4.2.1
        have s4_2_2 : dist B O = 0 := by
          rw [dist_comm O A] at s4_2_1
          exact (by linarith only [hH6, s4_2_1])
        -- 4.2.3. mun:distance-zero P := B, Q := O, from 4.2.2
        have s4_2_3 : B = O := by exact ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := B) (Q := O))).mp s4_2_2
        -- 4.2.4. transitivity, from C1, 4.2.3
        exact Eq.trans hC1.symm s4_2_3.symm
      · skip
        -- 4.2.5. def:midpoint M := O, from C2, H6
        have s4_2_5 : Sbtw ℝ A O B ∧ dist A O = dist O B := ((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := O))).mpr ⟨hC2, (by (have h := hH6; rw [dist_comm B O] at h; exact h) : dist A O = dist O B)⟩
        -- 4.2.6. mun:midpoint-unique M := O, N := M, from H5, 4.2.5
        have s4_2_6 : O = M := by exact (Parley.Items.Stdlib.Geometry.mun_midpoint_unique (A := A) (B := B) (M := O) (N := M) s4_2_5 hH5)
        -- 4.2.7. restate H7
        have s4_2_7 : O ≠ M := by exact hH7
        exact absurd s4_2_6 s4_2_7
      · skip
        -- 4.2.8. mun:distance-zero P := O, Q := B, from C3
        have s4_2_8 : dist O B = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := O) (Q := B))).mpr hC3
        -- 4.2.9. transitivity, from H6, 4.2.8
        have s4_2_9 : dist A O = 0 := by
          rw [dist_comm O B] at s4_2_8
          exact (by linarith only [hH6, s4_2_8])
        -- 4.2.10. mun:distance-zero P := A, Q := O, from 4.2.9
        have s4_2_10 : A = O := by exact ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := A) (Q := O))).mp s4_2_9
        -- 4.2.11. transitivity, from C3, 4.2.10
        exact (Eq.trans hC3.symm s4_2_10.symm).symm
      · skip
        -- 4.2.12. mun:segment-addition P := A, Q := O, S := B, from C4
        have s4_2_12 : dist A B + dist B O = dist A O := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := O) (S := B) hC4)
        -- 4.2.13. algebra, from H6, 4.2.12
        have s4_2_13 : dist A B = 0 := by linear_combination hH6 + s4_2_12
        -- 4.2.14. mun:distance-zero P := A, Q := B, from 4.2.13
        exact ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := A) (Q := B))).mp s4_2_13
      · skip
        -- 4.2.15. mun:segment-addition P := O, Q := B, S := A, from C5
        have s4_2_15 : dist O A + dist A B = dist O B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := O) (Q := B) (S := A) hC5)
        -- 4.2.16. algebra, from H6, 4.2.15
        have s4_2_16 : dist A B = 0 := by
          rw [dist_comm O B, dist_comm O A] at s4_2_15
          exact (by linear_combination (-1) * hH6 + s4_2_15)
        -- 4.2.17. mun:distance-zero P := A, Q := B, from 4.2.16
        exact ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := A) (Q := B))).mp s4_2_16
    -- 4.3. restate 2
    have s4_3 : A ≠ B := by exact s2
    exact s4_3 s4_2
  -- 5. mun:triangle-off-line P := O, Q := A, R := B, from 2, 4
  have s5 : LeanBridges.Geometry.Triangle O A B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := O) (Q := A) (R := B) s2 s4)
  -- 6. mun:triangle-on-side P := O, Q := A, R := B, S := M, from 1, 5
  have s6 : LeanBridges.Geometry.Triangle O A M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := O) (Q := A) (R := B) (S := M) s5 s1a)
  -- 7. mun:triangle-on-side P := O, Q := B, R := A, S := M, from 1, 5
  have s7 : LeanBridges.Geometry.Triangle O B M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := O) (Q := B) (R := A) (S := M) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_23 O A B] at h; exact h) : LeanBridges.Geometry.Triangle O B A) (by (have h := s1a; rw [sbtw_comm (x := A) (y := M) (z := B)] at h; exact h) : Sbtw ℝ B M A))
  -- 8. thm:side-side-side B := M, C := O, D := B, E := M, F := O, from H6, 1, 6, 7
  have s8 : dist A M = dist B M ∧ dist M O = dist M O ∧ dist O A = dist O B ∧ EuclideanGeometry.angle A M O = EuclideanGeometry.angle B M O ∧ EuclideanGeometry.angle M O A = EuclideanGeometry.angle M O B ∧ EuclideanGeometry.angle O A M = EuclideanGeometry.angle O B M := by exact (Parley.Stdlib.Geometry.SideSideSide.side_side_side (A := A) (B := M) (C := O) (D := B) (E := M) (F := O) (by (have h := s6; rw [LeanBridges.Geometry.triangle_rot_231 O A M] at h; exact h) : LeanBridges.Geometry.Triangle A M O) (by (have h := s7; rw [LeanBridges.Geometry.triangle_rot_231 O B M] at h; exact h) : LeanBridges.Geometry.Triangle B M O) (by (have h := s1b; rw [dist_comm M B] at h; exact h) : dist A M = dist B M) rfl (by (have h := hH6; rw [dist_comm A O, dist_comm B O] at h; exact h) : dist O A = dist O B))
  -- 9. def:congruent P := A, Q := M, R := O, P′ := B, Q′ := M, R′ := O, from 6, 7, 8
  have s9 : ((((dist A M = dist B M ∧ dist M O = dist M O) ∧ dist O A = dist O B) ∧ EuclideanGeometry.angle A M O = EuclideanGeometry.angle B M O) ∧ EuclideanGeometry.angle M O A = EuclideanGeometry.angle M O B) ∧ EuclideanGeometry.angle O A M = EuclideanGeometry.angle O B M := by exact ((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := B) (Q := M) (Q' := M) (R := O) (R' := O) (by (have h := s6; rw [LeanBridges.Geometry.triangle_rot_231 O A M] at h; exact h) : LeanBridges.Geometry.Triangle A M O) (by (have h := s7; rw [LeanBridges.Geometry.triangle_rot_231 O B M] at h; exact h) : LeanBridges.Geometry.Triangle B M O))).mp s8
  -- 10. axi:supplementary-angles B := M, C := B, D := O, from H7, 1, 5
  have s10 : EuclideanGeometry.angle A M O + EuclideanGeometry.angle O M B = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := A) (B := M) (C := B) (D := O) s1a hH7 s5.1 s5.2.2.1)
  -- 11. mun:angle-turned P := B, Q := M, R := O, from H7, 3, 5
  have s11 : EuclideanGeometry.angle B M O = EuclideanGeometry.angle O M B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := B) (Q := M) (R := O) s3b hH7 (Ne.symm s5.2.2.1))
  -- 12. algebra, from 9, 10, 11
  linear_combination ((-90) / ((180))) * s9.1.1.2 + ((16200) / ((180) * (180))) * s10 + ((-90) / ((180))) * s11

end Parley.Stdlib.Geometry.ChordMidpointRightAngle
