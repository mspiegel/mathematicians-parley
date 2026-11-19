module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
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
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.BetweenSplit
public import Parley.Stdlib.Geometry.ChordMidpointRightAngle
public import Parley.Stdlib.Geometry.CircleCentreApart
public import Parley.Stdlib.Geometry.OffLineAlong
public import Parley.Stdlib.Geometry.OnLineOther
public import Parley.Stdlib.Geometry.Pythagoras
public import Parley.Stdlib.Geometry.RightAngleAlong

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.PowerOfAPoint

theorem power_of_a_point (A : ℂ) (B : ℂ) (P : ℂ) (O : ℂ) (hH5 : Sbtw ℝ A P B) (hH6 : dist A O = dist B O) :
    dist A O ^ 2 - dist P O ^ 2 = dist P A * dist P B := by
  -- 1. mun:between-ends-apart R := P, S := A, T := B, from H5
  have s1 : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := P) (S := A) (T := B) hH5)
  -- 2. obtain M: mun:midpoint-exists, from 1
  obtain ⟨M, s2a, s2b⟩ := (Parley.Items.Stdlib.Geometry.mun_midpoint_exists (A := A) (B := B) s1)
  -- 3. def:midpoint, from 2
  have s3a : Sbtw ℝ A M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp s2b).1
  have s3b : dist A M = dist M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp s2b).2
  -- 4. mun:between-apart R := M, S := A, T := B, from 3
  have s4a : A ≠ M := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := M) (S := A) (T := B) s3a)
  have s4b : B ≠ M := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := M) (S := A) (T := B) s3a)
  -- 5. mun:segment-addition P := A, Q := B, S := P, from H5
  have s5 : dist A P + dist P B = dist A B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := B) (S := P) hH5)
  -- 6. mun:segment-addition P := A, Q := B, S := M, from 3
  have s6 : dist A M + dist M B = dist A B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := B) (S := M) s3a)
  -- 7. axi:excluded-middle P := O = M
  have s7 : O = M ∨ O ≠ M := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := O = M))
  -- 8. cases, from 7
  have s8 : dist A O ^ 2 - dist P O ^ 2 = dist A M ^ 2 - dist P M ^ 2 := by
    rcases s7 with hC1 | hC2
    · skip
      -- 8.1. algebra
      have s8_1 : dist A M ^ 2 - dist P M ^ 2 = dist A M ^ 2 - dist P M ^ 2 := by ring1
      -- 8.2. substitute O = M (C1) into line 8.1
      exact Eq.subst (motive := (fun t : ℂ => dist A t ^ 2 - dist P t ^ 2 = dist A M ^ 2 - dist P M ^ 2)) hC1.symm s8_1
    · skip
      -- 8.3. mun:circle-centre-apart X := A, Y := B, from H6, 1
      have s8_3 : A ≠ O := by exact (Parley.Stdlib.Geometry.CircleCentreApart.circle_centre_apart (X := A) (Y := B) (O := O) s1 hH6)
      -- 8.4. mun:circle-centre-apart X := B, Y := A, from H6, 1
      have s8_4 : B ≠ O := by exact (Parley.Stdlib.Geometry.CircleCentreApart.circle_centre_apart (X := B) (Y := A) (O := O) (Ne.symm s1) hH6.symm)
      -- 8.5. thm:chord-midpoint-right-angle, from C2, H6, 2, 4, 8.4
      have s8_5 : EuclideanGeometry.angle O M B = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.ChordMidpointRightAngle.chord_midpoint_right_angle (A := A) (B := B) (M := M) (O := O) s2b hH6 hC2 (Ne.symm s4b) (Ne.symm s8_4))
      -- 8.6. axi:supplementary-angles B := M, C := B, D := O, from C2, 3, 8.3, 8.4
      have s8_6 : EuclideanGeometry.angle A M O + EuclideanGeometry.angle O M B = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := A) (B := M) (C := B) (D := O) s3a hC2 (Ne.symm s8_3) (Ne.symm s8_4))
      -- 8.7. mun:angle-turned P := O, Q := M, R := A, from C2, 4, 8.3
      have s8_7 : EuclideanGeometry.angle O M A = EuclideanGeometry.angle A M O := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := O) (Q := M) (R := A) hC2 s4a (Ne.symm s8_3))
      -- 8.8. algebra, from 8.5, 8.6, 8.7
      have s8_8 : EuclideanGeometry.angle O M A = (90 : ℝ) * Real.pi / 180 := by linear_combination ((-32400) / ((180) * (180))) * s8_5 + ((32400) / ((180) * (180))) * s8_6 + ((180) / ((180))) * s8_7
      -- 8.9. mun:right-angle-triangle P := O, Q := M, R := A, from C2, 4, 8.3, 8.8
      have s8_9 : LeanBridges.Geometry.Triangle O M A := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := O) (Q := M) (R := A) hC2 s4a s8_8 (Ne.symm s8_3))
      -- 8.10. thm:pythagoras A := O, B := A, C := M, from 8.8, 8.9
      have s8_10 : dist O A ^ 2 = dist O M ^ 2 + dist A M ^ 2 := by exact (Parley.Stdlib.Geometry.Pythagoras.pythagoras (A := O) (B := A) (C := M) (by (have h := s8_9; rw [LeanBridges.Geometry.triangle_swap_23 O M A] at h; exact h) : LeanBridges.Geometry.Triangle O A M) s8_8)
      -- 8.11. axi:excluded-middle P := P = M
      have s8_11 : P = M ∨ P ≠ M := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P = M))
      -- 8.12. cases, from 8.11
      have s8_12 : dist P O ^ 2 = dist O M ^ 2 + dist P M ^ 2 := by
        rcases s8_11 with hC3 | hC4
        · skip
          -- 8.12.1. mun:distance-zero Q := M, from C3
          have s8_12_1 : dist P M = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := P) (Q := M))).mpr hC3
          -- 8.12.2. algebra, from 8.12.1
          have s8_12_2 : dist M O ^ 2 = dist O M ^ 2 + dist P M ^ 2 := by
            rw [dist_comm P M] at s8_12_1
            rw [dist_comm O M, dist_comm P M]
            exact (by linear_combination (-dist M P) * s8_12_1)
          -- 8.12.3. substitute P = M (C3) into line 8.12.2
          exact Eq.subst (motive := (fun t : ℂ => dist t O ^ 2 = dist O M ^ 2 + dist P M ^ 2)) hC3.symm s8_12_2
        · skip
          -- 8.12.4. mun:between-collinear R := M, S := A, T := B, from 3
          have s8_12_4 : Collinear ℝ {B, M, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := M) (S := A) (T := B) s3a)
          -- 8.12.5. def:on-line P := M, from 1, 8.12.4
          have s8_12_5 : M ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := M) s1)).mpr (by (have h := s8_12_4; rw [LeanBridges.Geometry.collinear_rot_312 B M A] at h; exact h) : Collinear ℝ {A, B, M})
          -- 8.12.6. mun:between-collinear R := P, S := A, T := B, from H5
          have s8_12_6 : Collinear ℝ {B, P, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := P) (S := A) (T := B) hH5)
          -- 8.12.7. def:on-line, from 1, 8.12.6
          have s8_12_7 : P ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := P) s1)).mpr (by (have h := s8_12_6; rw [LeanBridges.Geometry.collinear_rot_312 B P A] at h; exact h) : Collinear ℝ {A, B, P})
          -- 8.12.8. mun:on-line-ends, from 1
          have s8_12_8a : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) s1)
          have s8_12_8b : B ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := B) s1)
          -- 8.12.9. mun:on-line-other X := M, Y := B, Z := P, from 1, 4, 8.12.5, 8.12.7, 8.12.8
          have s8_12_9 : P ∈ LeanBridges.Geometry.line M B := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := A) (B := B) (X := M) (Y := B) (Z := P) s1 (Ne.symm s4b) s8_12_5 s8_12_8b s8_12_7)
          -- 8.12.10. mun:right-angle-triangle P := O, Q := M, R := B, from C2, 4, 8.4, 8.5
          have s8_12_10 : LeanBridges.Geometry.Triangle O M B := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := O) (Q := M) (R := B) hC2 s4b s8_5 (Ne.symm s8_4))
          -- 8.12.11. mun:triangle-not-on-line P := O, Q := M, R := B, from 8.12.10
          have s8_12_11 : ¬ O ∈ LeanBridges.Geometry.line M B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := O) (Q := M) (R := B) s8_12_10)
          -- 8.12.12. mun:on-off-apart A := M, X := P, Y := O, from 8.12.9, 8.12.11
          have s8_12_12 : P ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := M) (B := B) (X := P) (Y := O) s8_12_9 s8_12_11)
          -- 8.12.13. mun:right-angle-along P := O, H := M, S := B, T := P, from 4, 8.4, 8.5, 8.12.9
          have r2167_1 : ¬ O ∈ LeanBridges.Geometry.line M P := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := M) (B := B) (X := P) (P := O) (Ne.symm s4b) s8_12_9 hC4 s8_12_11)
          have r2167_2 : LeanBridges.Geometry.Triangle O M P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := O) (Q := M) (R := P) (Ne.symm hC4) r2167_1)
          have s8_12_13 : EuclideanGeometry.angle O M P = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.RightAngleAlong.right_angle_along (P := O) (H := M) (S := B) (T := P) r2167_2.1 s4b s8_5 s8_12_9 (Ne.symm r2167_2.2.1) (Ne.symm s8_4) r2167_2)
          -- 8.12.14. mun:right-angle-triangle P := O, Q := M, R := P, from C2, C4, 8.12.12, 8.12.13
          have s8_12_14 : LeanBridges.Geometry.Triangle O M P := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := O) (Q := M) (R := P) hC2 hC4 s8_12_13 (Ne.symm s8_12_12))
          -- 8.12.15. thm:pythagoras A := O, B := P, C := M, from 8.12.13, 8.12.14
          have s8_12_15 : dist O P ^ 2 = dist O M ^ 2 + dist P M ^ 2 := by exact (Parley.Stdlib.Geometry.Pythagoras.pythagoras (A := O) (B := P) (C := M) (by (have h := s8_12_14; rw [LeanBridges.Geometry.triangle_swap_23 O M P] at h; exact h) : LeanBridges.Geometry.Triangle O P M) s8_12_13)
          exact (by (have h := s8_12_15; rw [dist_comm O P] at h; exact h) : dist P O ^ 2 = dist O M ^ 2 + dist P M ^ 2)
      -- 8.13. algebra, from 8.10, 8.12
      rw [dist_comm O A, dist_comm O M] at s8_10
      rw [dist_comm P O, dist_comm O M, dist_comm P M] at s8_12
      rw [dist_comm P O, dist_comm P M]
      exact (by linear_combination s8_10 + (-1) * s8_12)
  -- 9. mun:between-split, from H5, 3
  have s9 : (P = M ∨ Sbtw ℝ A P M) ∨ Sbtw ℝ M P B := by exact (Parley.Stdlib.Geometry.BetweenSplit.between_split (A := A) (B := B) (M := M) (P := P) s3a hH5)
  -- 10. cases, from 9
  have s10 : dist P A * dist P B = dist A M ^ 2 - dist P M ^ 2 := by
    rcases s9 with (hC5 | hC6) | hC7
    · skip
      -- 10.1. mun:distance-zero Q := M, from C5
      have s10_1 : dist P M = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := P) (Q := M))).mpr hC5
      -- 10.2. algebra, from 3
      have s10_2 : dist M A * dist M B = dist A M ^ 2 := by
        rw [dist_comm M B] at s3b
        rw [dist_comm M A, dist_comm M B]
        exact (by linear_combination (-dist A M) * s3b)
      -- 10.3. algebra, from 10.1, 10.2
      have s10_3 : dist M A * dist M B = dist A M ^ 2 - dist P M ^ 2 := by
        rw [dist_comm P M] at s10_1
        rw [dist_comm M A, dist_comm M B] at s10_2
        rw [dist_comm M A, dist_comm M B, dist_comm P M]
        exact (by linear_combination (dist M P) * s10_1 + s10_2)
      -- 10.4. substitute P = M (C5) into line 10.3
      exact Eq.subst (motive := (fun t : ℂ => dist t A * dist t B = dist A M ^ 2 - dist P M ^ 2)) hC5.symm s10_3
    · skip
      -- 10.5. mun:segment-addition P := A, Q := M, S := P, from C6
      have s10_5 : dist A P + dist P M = dist A M := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := M) (S := P) hC6)
      -- 10.6. algebra, from 10.5
      have s10_6 : dist P A = dist A M - dist P M := by
        rw [dist_comm P M] at s10_5
        rw [dist_comm P A, dist_comm P M]
        exact (by linear_combination s10_5)
      -- 10.7. algebra, from 3, 5, 6, 10.5
      have s10_7 : dist P B = dist A M + dist P M := by linear_combination (-1) * s3b + s5 + (-1) * s6 + (-1) * s10_5
      -- 10.8. algebra, from 10.6
      have s10_8 : dist P A * dist P B = (dist A M - dist P M) * dist P B := by linear_combination (dist P B) * s10_6
      -- 10.9. algebra, from 10.7
      have s10_9 : (dist A M - dist P M) * dist P B = dist A M ^ 2 - dist P M ^ 2 := by linear_combination (dist A M - dist P M) * s10_7
      -- 10.10. transitivity, from 10.8, 10.9
      exact Eq.trans s10_8 s10_9
    · skip
      -- 10.11. mun:segment-addition P := M, Q := B, S := P, from C7
      have s10_11 : dist M P + dist P B = dist M B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := M) (Q := B) (S := P) hC7)
      -- 10.12. algebra, from 3, 10.11
      have s10_12 : dist P B = dist A M - dist P M := by
        rw [dist_comm M B] at s3b
        rw [dist_comm M B, dist_comm P B] at s10_11
        rw [dist_comm P B, dist_comm P M]
        exact (by linear_combination (-1) * s3b + s10_11)
      -- 10.13. algebra, from 5, 6, 10.11
      have s10_13 : dist P A = dist A M + dist P M := by
        rw [dist_comm P B] at s5
        rw [dist_comm M B] at s6
        rw [dist_comm M B, dist_comm P B] at s10_11
        rw [dist_comm P A, dist_comm P M]
        exact (by linear_combination s5 + (-1) * s6 + (-1) * s10_11)
      -- 10.14. algebra, from 10.13
      have s10_14 : dist P A * dist P B = (dist A M + dist P M) * dist P B := by linear_combination (dist P B) * s10_13
      -- 10.15. algebra, from 10.12
      have s10_15 : (dist A M + dist P M) * dist P B = dist A M ^ 2 - dist P M ^ 2 := by linear_combination (dist A M + dist P M) * s10_12
      -- 10.16. transitivity, from 10.14, 10.15
      exact Eq.trans s10_14 s10_15
  -- 11. transitivity, from 8, 10
  exact Eq.trans s8 s10.symm

end Parley.Stdlib.Geometry.PowerOfAPoint
