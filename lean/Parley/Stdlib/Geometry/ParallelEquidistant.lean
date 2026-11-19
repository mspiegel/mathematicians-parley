module

public import Geometry
public import Batteries.Tactic.Init
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
public import Parley.Stdlib.Geometry.AlternateAngles
public import Parley.Stdlib.Geometry.AlternateAnglesConverse
public import Parley.Stdlib.Geometry.OffLineAlong
public import Parley.Stdlib.Geometry.ParallelOff
public import Parley.Stdlib.Geometry.ParallelSameSide
public import Parley.Stdlib.Geometry.VerticalAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ParallelEquidistant

theorem parallel_equidistant (A : ℂ) (B : ℂ) (H : ℂ) (K : ℂ) (hH5 : A ≠ B) (hH6 : 0 < Complex.im ((A - H) / (K - H)) * Complex.im ((B - H) / (K - H))) (hH7 : Complex.im ((B - A) / (K - H)) = 0) (hH8 : EuclideanGeometry.angle A H K = (90 : ℝ) * Real.pi / 180) (hH9 : EuclideanGeometry.angle B K H = (90 : ℝ) * Real.pi / 180) :
    dist A H = dist B K := by
  -- 1. mun:same-side-off-line A := H, B := K, P := A, Q := B, from H6
  have s1a : H ≠ K := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_1 (A := H) (B := K) (P := A) (Q := B) hH6)
  have s1b : ¬ A ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := H) (B := K) (P := A) (Q := B) hH6)
  have s1c : ¬ B ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := H) (B := K) (P := A) (Q := B) hH6)
  -- 2. mun:off-line-apart A := H, B := K, P := A, from 1
  have s2a : A ≠ H := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := H) (B := K) (P := A) s1a s1b)
  have s2b : A ≠ K := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := H) (B := K) (P := A) s1a s1b)
  -- 3. mun:off-line-apart A := H, B := K, P := B, from 1
  have s3a : B ≠ H := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := H) (B := K) (P := B) s1a s1c)
  have s3b : B ≠ K := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := H) (B := K) (P := B) s1a s1c)
  -- 4. obtain M: mun:midpoint-exists B := K, from 2
  obtain ⟨M, s4a, s4b⟩ := (Parley.Items.Stdlib.Geometry.mun_midpoint_exists (A := A) (B := K) s2b)
  -- 5. def:midpoint B := K, from 4
  have s5a : Sbtw ℝ A M K := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := K) (M := M))).mp s4b).1
  have s5b : dist A M = dist M K := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := K) (M := M))).mp s4b).2
  -- 6. mun:on-line-ends A := H, B := K, from 1
  have s6a : H ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := H) (B := K) s1a)
  have s6b : K ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := H) (B := K) s1a)
  -- 7. mun:segment-off-line A := H, B := K, P := A, Q := K, X := M, from 1, 5, 6
  have s7 : 0 < Complex.im ((M - H) / (K - H)) * Complex.im ((A - H) / (K - H)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := H) (B := K) (P := A) (Q := K) (X := M) s1a s6b s1b s5a)
  -- 8. mun:same-side-off-line A := H, B := K, P := M, Q := A, from 7
  have s8 : ¬ M ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := H) (B := K) (P := M) (Q := A) s7)
  -- 9. mun:on-off-apart A := H, B := K, X := H, Y := M, from 6, 8
  have s9 : H ≠ M := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := H) (B := K) (X := H) (Y := M) s6a s8)
  -- 10. axi:distance-positive P := H, Q := M, from 9
  have s10 : dist H M > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := H) (Q := M) s9)
  -- 11. obtain Z: mun:segment-extension A := H, B := M, r := |HM|, from 9, 10
  obtain ⟨Z, s11a, ⟨s11b, s11c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := H) (B := M) (r := dist H M) s9 s10)
  -- 12. mun:triangle-off-line P := M, Q := H, R := K, from 1, 8
  have s12 : LeanBridges.Geometry.Triangle M H K := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := M) (Q := H) (R := K) s1a s8)
  -- 13. mun:triangle-extension P := H, Q := M, R := K, S := A, from 5, 12
  have s13 : LeanBridges.Geometry.Triangle H M A := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := H) (Q := M) (R := K) (S := A) (by (have h := s12; rw [LeanBridges.Geometry.triangle_swap_12 M H K] at h; exact h) : LeanBridges.Geometry.Triangle H M K) (by (have h := s5a; rw [sbtw_comm (x := A) (y := M) (z := K)] at h; exact h) : Sbtw ℝ K M A))
  -- 14. mun:triangle-extension P := K, Q := M, R := H, S := Z, from 11, 12
  have s14 : LeanBridges.Geometry.Triangle K M Z := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := K) (Q := M) (R := H) (S := Z) (by (have h := s12; rw [LeanBridges.Geometry.triangle_rot_312 M H K] at h; exact h) : LeanBridges.Geometry.Triangle K M H) s11b)
  -- 15. mun:triangle-extension P := A, Q := M, R := H, S := Z, from 11, 13
  have s15 : LeanBridges.Geometry.Triangle A M Z := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := A) (Q := M) (R := H) (S := Z) (by (have h := s13; rw [LeanBridges.Geometry.triangle_swap_13 H M A] at h; exact h) : LeanBridges.Geometry.Triangle A M H) s11b)
  -- 16. thm:vertical-angles A := H, B := K, C := Z, D := A, O := M, from 5, 11, 12, 15
  have s16 : EuclideanGeometry.angle H M K = EuclideanGeometry.angle Z M A := by exact (Parley.Stdlib.Geometry.VerticalAngles.vertical_angles (A := H) (B := K) (C := Z) (D := A) (O := M) s11b (by (have h := s5a; rw [sbtw_comm (x := A) (y := M) (z := K)] at h; exact h) : Sbtw ℝ K M A) (by (have h := s12; rw [LeanBridges.Geometry.triangle_swap_12 M H K] at h; exact h) : LeanBridges.Geometry.Triangle H M K) (by (have h := s15; rw [LeanBridges.Geometry.triangle_swap_13 A M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M A))
  -- 17. thm:vertical-angles A := H, B := A, C := Z, D := K, O := M, from 5, 11, 13, 14
  have s17 : EuclideanGeometry.angle H M A = EuclideanGeometry.angle Z M K := by exact (Parley.Stdlib.Geometry.VerticalAngles.vertical_angles (A := H) (B := A) (C := Z) (D := K) (O := M) s11b s5a s13 (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_13 K M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M K))
  -- 18. restate 11
  have s18 : dist H M = dist Z M := by exact (by (have h := s11c.symm; rw [dist_comm M Z] at h; exact h) : dist H M = dist Z M)
  -- 19. restate 5
  have s19 : dist M K = dist M A := by exact (by (have h := s5b.symm; rw [dist_comm A M] at h; exact h) : dist M K = dist M A)
  -- 20. axi:side-angle-side P := H, Q := M, R := K, P′ := Z, Q′ := M, R′ := A, from 12, 15, 16, 18, 19
  have s20 : dist H M = dist Z M ∧ dist M K = dist M A ∧ dist K H = dist A Z ∧ EuclideanGeometry.angle H M K = EuclideanGeometry.angle Z M A ∧ EuclideanGeometry.angle M K H = EuclideanGeometry.angle M A Z ∧ EuclideanGeometry.angle K H M = EuclideanGeometry.angle A Z M := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := H) (P' := Z) (Q := M) (Q' := M) (R := K) (R' := A) (by (have h := s12; rw [LeanBridges.Geometry.triangle_swap_12 M H K] at h; exact h) : LeanBridges.Geometry.Triangle H M K) (by (have h := s15; rw [LeanBridges.Geometry.triangle_swap_13 A M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M A) s18 s16 s19)
  -- 21. def:congruent, from 12, 15, 20
  have s21a : dist K H = dist A Z := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := H) (P' := Z) (Q := M) (Q' := M) (R := K) (R' := A) (by (have h := s12; rw [LeanBridges.Geometry.triangle_swap_12 M H K] at h; exact h) : LeanBridges.Geometry.Triangle H M K) (by (have h := s15; rw [LeanBridges.Geometry.triangle_swap_13 A M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M A))).mp s20).1.1.1.2
  have s21b : EuclideanGeometry.angle M K H = EuclideanGeometry.angle M A Z := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := H) (P' := Z) (Q := M) (Q' := M) (R := K) (R' := A) (by (have h := s12; rw [LeanBridges.Geometry.triangle_swap_12 M H K] at h; exact h) : LeanBridges.Geometry.Triangle H M K) (by (have h := s15; rw [LeanBridges.Geometry.triangle_swap_13 A M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M A))).mp s20).1.2
  -- 22. axi:side-angle-side P := H, Q := M, R := A, P′ := Z, Q′ := M, R′ := K, from 13, 14, 17, 18, 19
  have s22 : dist H M = dist Z M ∧ dist M A = dist M K ∧ dist A H = dist K Z ∧ EuclideanGeometry.angle H M A = EuclideanGeometry.angle Z M K ∧ EuclideanGeometry.angle M A H = EuclideanGeometry.angle M K Z ∧ EuclideanGeometry.angle A H M = EuclideanGeometry.angle K Z M := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := H) (P' := Z) (Q := M) (Q' := M) (R := A) (R' := K) s13 (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_13 K M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M K) s18 s17 s19.symm)
  -- 23. def:congruent, from 13, 14, 22
  have s23a : dist A H = dist K Z := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := H) (P' := Z) (Q := M) (Q' := M) (R := A) (R' := K) s13 (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_13 K M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M K))).mp s22).1.1.1.2
  have s23b : EuclideanGeometry.angle M A H = EuclideanGeometry.angle M K Z := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := H) (P' := Z) (Q := M) (Q' := M) (R := A) (R' := K) s13 (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_13 K M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M K))).mp s22).1.2
  have s23c : EuclideanGeometry.angle A H M = EuclideanGeometry.angle K Z M := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := H) (P' := Z) (Q := M) (Q' := M) (R := A) (R' := K) s13 (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_13 K M Z] at h; exact h) : LeanBridges.Geometry.Triangle Z M K))).mp s22).2
  -- 24. calculation
  have s24 : EuclideanGeometry.angle Z A K = EuclideanGeometry.angle A K H := by
    calc EuclideanGeometry.angle Z A K = EuclideanGeometry.angle K A Z := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := K) (Q := A) (R := Z) (Ne.symm s2b) (Ne.symm s15.2.2.1) s14.2.2.1).symm
      _ = EuclideanGeometry.angle M A Z := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := A) (Q := K) (R := Z) (S := M) s5a (Ne.symm s15.2.2.1) (Ne.symm s14.2.1) (Ne.symm s14.2.2.1)).symm
      _ = EuclideanGeometry.angle M K H := s21b.symm
      _ = EuclideanGeometry.angle A K H := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := K) (Q := A) (R := H) (S := M) (by (have h := s5a; rw [sbtw_comm (x := A) (y := M) (z := K)] at h; exact h) : Sbtw ℝ K M A) s1a s9 (Ne.symm s2a))
  -- 25. mun:triangle-off-line P := A, Q := H, R := K, from 1
  have s25 : LeanBridges.Geometry.Triangle A H K := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := A) (Q := H) (R := K) s1a s1b)
  -- 26. mun:triangle-not-on-line P := H, Q := A, R := K, from 25
  have s26 : ¬ H ∈ LeanBridges.Geometry.line A K := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := H) (Q := A) (R := K) (by (have h := s25; rw [LeanBridges.Geometry.triangle_swap_12 A H K] at h; exact h) : LeanBridges.Geometry.Triangle H A K))
  -- 27. mun:between-collinear R := M, S := A, T := K, from 5
  have s27 : Collinear ℝ {K, M, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := M) (S := A) (T := K) s5a)
  -- 28. def:on-line P := M, B := K, from 2, 27
  have s28 : M ∈ LeanBridges.Geometry.line A K := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := K) (P := M) s2b)).mpr (by (have h := s27; rw [LeanBridges.Geometry.collinear_rot_312 K M A] at h; exact h) : Collinear ℝ {A, K, M})
  -- 29. mun:segment-across-line B := K, P := H, Q := Z, from 2, 11, 26, 28
  have s29 : Complex.im ((H - A) / (K - A)) * Complex.im ((Z - A) / (K - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := A) (B := K) (M := M) (P := H) (Q := Z) s2b s28 s26 s11b)
  -- 30. thm:alternate-angles-converse P := K, Q := H, R := A, S := Z, from 24, 25, 29
  have s30 : Complex.im ((Z - A) / (H - K)) = 0 := by exact (Parley.Stdlib.Geometry.AlternateAnglesConverse.alternate_angles_converse (P := K) (Q := H) (R := A) (S := Z) (by (have h := s25; rw [LeanBridges.Geometry.triangle_swap_13 A H K] at h; exact h) : LeanBridges.Geometry.Triangle K H A) (by (have h := s29; rw [mul_comm (Complex.im ((H - A) / (K - A))) (Complex.im ((Z - A) / (K - A)))] at h; exact h) : Complex.im ((Z - A) / (K - A)) * Complex.im ((H - A) / (K - A)) < 0) s24)
  -- 31. mun:on-line-ends, from H5
  have s31 : B ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := B) hH5)
  -- 32. mun:parallel-along C := H, D := K, E := B, from H5, H7, 31
  have s32 : Complex.im ((B - A) / (H - K)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := A) (B := B) (C := H) (D := K) (E := B) hH7 hH5 s31 (Ne.symm hH5))
  -- 33. mun:triangle-not-on-line P := A, Q := K, R := H, from 25
  have s33 : ¬ A ∈ LeanBridges.Geometry.line K H := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := A) (Q := K) (R := H) (by (have h := s25; rw [LeanBridges.Geometry.triangle_swap_23 A H K] at h; exact h) : LeanBridges.Geometry.Triangle A K H))
  -- 34. axi:parallel-uniqueness A := K, B := H, P := A, C := Z, D := B, from H5, 1, 15, 30, 32, 33
  have s34 : LeanBridges.Geometry.line A Z = LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.axi_parallel_uniqueness (A := K) (B := H) (C := Z) (D := B) (P := A) (Ne.symm s1a) s33 s15.2.2.1 hH5 s30 s32)
  -- 35. mun:on-line-ends B := Z, from 15
  have s35a : A ∈ LeanBridges.Geometry.line A Z := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := Z) s15.2.2.1)
  have s35b : Z ∈ LeanBridges.Geometry.line A Z := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := Z) s15.2.2.1)
  -- 36. substitute line AZ = line AB (line 34) into line 35
  have s36 : Z ∈ LeanBridges.Geometry.line A B := Eq.subst (motive := (fun t : Set ℂ => Z ∈ t)) s34 s35b
  -- 37. mun:parallel-same-side C := H, D := K, X := Z, from H5, H7, 1, 15, 36
  have s37 : 0 < Complex.im ((Z - H) / (K - H)) * Complex.im ((A - H) / (K - H)) := by exact (Parley.Stdlib.Geometry.ParallelSameSide.parallel_same_side (A := A) (B := B) (C := H) (D := K) (X := Z) hH5 s1a hH7 s1b s36 (Ne.symm s15.2.2.1))
  -- 38. mun:same-side-same A := H, B := K, P := Z, Q := A, R := B, from H6, 37
  have s38 : 0 < Complex.im ((Z - H) / (K - H)) * Complex.im ((B - H) / (K - H)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := H) (B := K) (P := Z) (Q := A) (R := B) s37 hH6)
  -- 39. mun:between-ends-apart R := M, S := H, T := Z, from 11
  have s39 : H ≠ Z := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := M) (S := H) (T := Z) s11b)
  -- 40. mun:between-collinear R := M, S := H, T := Z, from 11
  have s40 : Collinear ℝ {H, M, Z} := (by (have h := (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := M) (S := H) (T := Z) s11b); rw [LeanBridges.Geometry.collinear_swap_13 Z M H] at h; exact h) : Collinear ℝ {H, M, Z})
  -- 41. def:on-line P := Z, A := H, B := M, from 9, 40
  have s41 : Z ∈ LeanBridges.Geometry.line H M := ((Parley.Items.Stdlib.Geometry.def_on_line (A := H) (B := M) (P := Z) s9)).mpr s40
  -- 42. mun:triangle-not-on-line P := A, Q := H, R := M, from 13
  have s42 : ¬ A ∈ LeanBridges.Geometry.line H M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := A) (Q := H) (R := M) (by (have h := s13; rw [LeanBridges.Geometry.triangle_rot_312 H M A] at h; exact h) : LeanBridges.Geometry.Triangle A H M))
  -- 43. mun:off-line-along A := H, B := M, X := Z, P := A, from 9, 39, 41, 42
  have s43 : ¬ A ∈ LeanBridges.Geometry.line H Z := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := H) (B := M) (X := Z) (P := A) s9 s41 (Ne.symm s39) s42)
  -- 44. def:on-line P := M, A := H, B := Z, from 39, 40
  have s44 : M ∈ LeanBridges.Geometry.line H Z := ((Parley.Items.Stdlib.Geometry.def_on_line (A := H) (B := Z) (P := M) s39)).mpr (by (have h := s40; rw [LeanBridges.Geometry.collinear_swap_23 H M Z] at h; exact h) : Collinear ℝ {H, Z, M})
  -- 45. mun:segment-across-line A := H, B := Z, P := A, Q := K, from 5, 39, 43, 44
  have s45 : Complex.im ((A - H) / (Z - H)) * Complex.im ((K - H) / (Z - H)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := H) (B := Z) (M := M) (P := A) (Q := K) s39 s44 s43 s5a)
  -- 46. mun:triangle-not-on-line P := K, Q := Z, R := M, from 14
  have s46 : ¬ K ∈ LeanBridges.Geometry.line Z M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := K) (Q := Z) (R := M) (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_23 K M Z] at h; exact h) : LeanBridges.Geometry.Triangle K Z M))
  -- 47. def:on-line P := H, A := Z, B := M, from 14, 40
  have s47 : H ∈ LeanBridges.Geometry.line Z M := ((Parley.Items.Stdlib.Geometry.def_on_line (A := Z) (B := M) (P := H) (Ne.symm s14.2.1))).mpr (by (have h := s40; rw [LeanBridges.Geometry.collinear_swap_13 H M Z] at h; exact h) : Collinear ℝ {Z, M, H})
  -- 48. mun:off-line-along A := Z, B := M, X := H, P := K, from 14, 39, 46, 47
  have s48 : ¬ K ∈ LeanBridges.Geometry.line Z H := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := Z) (B := M) (X := H) (P := K) (Ne.symm s14.2.1) s47 s39 s46)
  -- 49. mun:triangle-off-line P := K, Q := Z, R := H, from 39, 48
  have s49 : LeanBridges.Geometry.Triangle K Z H := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := K) (Q := Z) (R := H) (Ne.symm s39) s48)
  -- 50. calculation
  have s50 : EuclideanGeometry.angle A H Z = EuclideanGeometry.angle H Z K := by
    calc EuclideanGeometry.angle A H Z = EuclideanGeometry.angle Z H A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := A) (Q := H) (R := Z) s2a (Ne.symm s39) s15.2.2.1)
      _ = EuclideanGeometry.angle M H A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := H) (Q := Z) (R := A) (S := M) s11b s2a s15.1 s15.2.2.1).symm
      _ = EuclideanGeometry.angle A H M := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := A) (Q := H) (R := M) s2a (Ne.symm s9) s15.1).symm
      _ = EuclideanGeometry.angle K Z M := s23c
      _ = EuclideanGeometry.angle M Z K := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := K) (Q := Z) (R := M) s14.2.2.1 s14.2.1 s14.1)
      _ = EuclideanGeometry.angle H Z K := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := Z) (Q := H) (R := K) (S := M) (by (have h := s11b; rw [sbtw_comm (x := H) (y := M) (z := Z)] at h; exact h) : Sbtw ℝ Z M H) s14.2.2.1 s14.1 (Ne.symm s1a))
  -- 51. thm:alternate-angles-converse P := Z, Q := K, R := H, S := A, from 45, 49, 50
  have s51 : Complex.im ((A - H) / (K - Z)) = 0 := by exact (Parley.Stdlib.Geometry.AlternateAnglesConverse.alternate_angles_converse (P := Z) (Q := K) (R := H) (S := A) (by (have h := s49; rw [LeanBridges.Geometry.triangle_swap_12 K Z H] at h; exact h) : LeanBridges.Geometry.Triangle Z K H) s45 s50)
  -- 52. mun:on-line-ends A := H, B := A, from 2
  have s52a : H ∈ LeanBridges.Geometry.line H A := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := H) (B := A) (Ne.symm s2a))
  have s52b : A ∈ LeanBridges.Geometry.line H A := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := H) (B := A) (Ne.symm s2a))
  -- 53. mun:parallel-along A := H, B := A, C := Z, D := K, E := A, from 2, 51, 52
  have s53 : Complex.im ((A - H) / (Z - K)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := H) (B := A) (C := Z) (D := K) (E := A) s51 (Ne.symm s2a) s52b s2a)
  -- 54. mun:parallel-turned A := H, B := A, C := K, D := Z, from 2, 53
  have s54 : Complex.im ((Z - K) / (A - H)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_turned (A := H) (B := A) (C := K) (D := Z) (Ne.symm s2a) s53)
  -- 55. axi:distance-positive P := Z, Q := K, from 14
  have s55 : dist Z K > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := Z) (Q := K) (Ne.symm s14.2.2.1))
  -- 56. obtain W: mun:segment-extension A := Z, B := K, r := |ZK|, from 14, 55
  obtain ⟨W, s56a, ⟨s56b, s56c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := Z) (B := K) (r := dist Z K) (Ne.symm s14.2.2.1) s55)
  -- 57. mun:between-apart R := K, S := Z, T := W, from 56
  have s57a : Z ≠ K := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := K) (S := Z) (T := W) s56b)
  have s57b : W ≠ K := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := K) (S := Z) (T := W) s56b)
  -- 58. mun:between-collinear R := K, S := Z, T := W, from 56
  have s58 : Collinear ℝ {W, K, Z} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := K) (S := Z) (T := W) s56b)
  -- 59. def:on-line P := W, A := K, B := Z, from 57, 58
  have s59 : W ∈ LeanBridges.Geometry.line K Z := ((Parley.Items.Stdlib.Geometry.def_on_line (A := K) (B := Z) (P := W) (Ne.symm s57a))).mpr (by (have h := s58; rw [LeanBridges.Geometry.collinear_rot_231 W K Z] at h; exact h) : Collinear ℝ {K, Z, W})
  -- 60. mun:parallel-along A := K, B := Z, C := H, D := A, E := W, from 54, 57, 59
  have s60 : Complex.im ((W - K) / (H - A)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := K) (B := Z) (C := H) (D := A) (E := W) s54 (Ne.symm s57a) s59 s57b)
  -- 61. mun:on-line-ends A := K, B := W, from 57
  have s61 : W ∈ LeanBridges.Geometry.line K W := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := K) (B := W) (Ne.symm s57b))
  -- 62. mun:parallel-along A := K, B := W, C := A, D := H, E := W, from 57, 60, 61
  have s62 : Complex.im ((W - K) / (A - H)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := K) (B := W) (C := A) (D := H) (E := W) s60 (Ne.symm s57b) s61 s57b)
  -- 63. mun:same-side-off-line A := H, B := K, P := Z, Q := A, from 37
  have s63 : ¬ Z ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := H) (B := K) (P := Z) (Q := A) s37)
  -- 64. mun:segment-across-line A := H, B := K, P := Z, Q := W, M := K, from 1, 6, 56, 63
  have s64 : Complex.im ((Z - H) / (K - H)) * Complex.im ((W - H) / (K - H)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := H) (B := K) (M := K) (P := Z) (Q := W) s1a s6b s63 s56b)
  -- 65. mun:same-opposite-opposite A := H, B := K, P := A, Q := Z, R := W, from 37, 64
  have s65 : Complex.im ((A - H) / (K - H)) * Complex.im ((W - H) / (K - H)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := H) (B := K) (P := A) (Q := Z) (R := W) (by (have h := s37; rw [mul_comm (Complex.im ((Z - H) / (K - H))) (Complex.im ((A - H) / (K - H)))] at h; exact h) : 0 < Complex.im ((A - H) / (K - H)) * Complex.im ((Z - H) / (K - H))) s64)
  -- 66. mun:opposite-sides-of-line A := H, B := K, C := K, D := H, P := W, Q := A, from 1, 6, 65
  have s66 : Complex.im ((W - K) / (H - K)) * Complex.im ((A - K) / (H - K)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_of_line (A := H) (B := K) (C := K) (D := H) (P := W) (Q := A) s1a (Ne.symm s1a) s6b s6a (by (have h := s65; rw [mul_comm (Complex.im ((A - H) / (K - H))) (Complex.im ((W - H) / (K - H)))] at h; exact h) : Complex.im ((W - H) / (K - H)) * Complex.im ((A - H) / (K - H)) < 0))
  -- 67. thm:alternate-angles P := H, Q := A, R := K, S := W, from 25, 62, 66
  have s67 : EuclideanGeometry.angle W K H = EuclideanGeometry.angle K H A := by exact (Parley.Stdlib.Geometry.AlternateAngles.alternate_angles (P := H) (Q := A) (R := K) (S := W) (by (have h := s25; rw [LeanBridges.Geometry.triangle_swap_12 A H K] at h; exact h) : LeanBridges.Geometry.Triangle H A K) s62 s66)
  -- 68. mun:angle-turned P := K, Q := H, R := A, from 1, 2
  have s68 : EuclideanGeometry.angle K H A = EuclideanGeometry.angle A H K := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := K) (Q := H) (R := A) (Ne.symm s1a) s2a (Ne.symm s2b))
  -- 69. axi:supplementary-angles A := Z, B := K, C := W, D := H, from 1, 56
  have r3681_1 : H ≠ Z := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := H) (B := K) (P := Z) s1a s63)
  have r3681_2 : ¬ W ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := H) (B := K) (P := Z) (Q := W) s64)
  have r3681_3 : H ≠ W := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := H) (B := K) (P := W) s1a r3681_2)
  have s69 : EuclideanGeometry.angle Z K H + EuclideanGeometry.angle H K W = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := Z) (B := K) (C := W) (D := H) s56b s1a r3681_1 r3681_3)
  -- 70. mun:angle-turned P := H, Q := K, R := W, from 1, 57
  have r3687_1 : ¬ W ∈ LeanBridges.Geometry.line H K := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := H) (B := K) (P := Z) (Q := W) s64)
  have r3687_2 : H ≠ W := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := H) (B := K) (P := W) s1a r3687_1)
  have s70 : EuclideanGeometry.angle H K W = EuclideanGeometry.angle W K H := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := H) (Q := K) (R := W) s1a s57b r3687_2)
  -- 71. mun:angle-turned P := H, Q := K, R := Z, from 1, 57
  have r3692_1 : H ≠ Z := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := H) (B := K) (P := Z) s1a s63)
  have s71 : EuclideanGeometry.angle H K Z = EuclideanGeometry.angle Z K H := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := H) (Q := K) (R := Z) s1a s57a r3692_1)
  -- 72. calculation
  have r3696_1 : Z ≠ H := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := M) (S := H) (T := Z) s11b)
  have s72 : EuclideanGeometry.angle H K B = EuclideanGeometry.angle H K Z := by
    calc EuclideanGeometry.angle H K B = EuclideanGeometry.angle B K H := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := H) (Q := K) (R := B) s1a s3b (Ne.symm s3a))
      _ = (90 : ℝ) * Real.pi / 180 := hH9
      _ = EuclideanGeometry.angle H K Z := by linear_combination ((32400) / ((180) * (180))) * hH8 + ((180) / ((180))) * s67 + ((180) / ((180))) * s68 + ((-32400) / ((180) * (180))) * s69 + ((180) / ((180))) * s70 + ((-180) / ((180))) * s71
  -- 73. mun:triangle-off-line P := B, Q := H, R := K, from 1
  have s73 : LeanBridges.Geometry.Triangle B H K := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := B) (Q := H) (R := K) s1a s1c)
  -- 74. mun:same-side-of-line A := H, B := K, C := K, D := H, P := Z, Q := B, from 1, 6, 38
  have s74 : 0 < Complex.im ((Z - K) / (H - K)) * Complex.im ((B - K) / (H - K)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := H) (B := K) (C := K) (D := H) (P := Z) (Q := B) s1a (Ne.symm s1a) s6b s6a s38)
  -- 75. mun:same-side-same A := K, B := H, P := B, Q := Z, R := B, from 74
  have s75 : 0 < Complex.im ((B - K) / (H - K)) * Complex.im ((B - K) / (H - K)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := K) (B := H) (P := B) (Q := Z) (R := B) (by (have h := s74; rw [mul_comm (Complex.im ((Z - K) / (H - K))) (Complex.im ((B - K) / (H - K)))] at h; exact h) : 0 < Complex.im ((B - K) / (H - K)) * Complex.im ((Z - K) / (H - K))) s74)
  -- 76. axi:angle-construction-unique A := K, B := H, C := B, D := B, E := Z, from 72, 73, 74, 75
  have s76 : Z ∈ LeanBridges.Geometry.ray K B := by exact (Parley.Items.Stdlib.Geometry.axi_angle_construction_unique (E := Z) (A := K) (B := H) (C := B) (D := B) (by (have h := s73; rw [LeanBridges.Geometry.triangle_swap_13 B H K] at h; exact h) : LeanBridges.Geometry.Triangle K H B) s75 s74 s72)
  -- 77. mun:ray-on-line P := Z, A := K, from 76
  have s77 : Z ∈ LeanBridges.Geometry.line K B := by exact (Parley.Items.Stdlib.Geometry.mun_ray_on_line (P := Z) (A := K) (B := B) s76)
  -- 78. contradiction
  have s78 : Z = B := by
    by_contra (hS1 : Z ≠ B)
    -- 78.1. axi:line-uniqueness A := Z, C := A, D := B, from H5, S1, 31, 36
    have s78_1 : LeanBridges.Geometry.line Z B = LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := Z) (B := B) (C := A) (D := B) hS1 hH5 s36 s31)
    -- 78.2. mun:on-line-ends A := K, from 3
    have s78_2a : K ∈ LeanBridges.Geometry.line K B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := K) (B := B) (Ne.symm s3b))
    have s78_2b : B ∈ LeanBridges.Geometry.line K B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := K) (B := B) (Ne.symm s3b))
    -- 78.3. axi:line-uniqueness A := Z, C := K, D := B, from S1, 3, 77, 78.2
    have s78_3 : LeanBridges.Geometry.line Z B = LeanBridges.Geometry.line K B := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := Z) (B := B) (C := K) (D := B) hS1 (Ne.symm s3b) s77 s78_2b)
    -- 78.4. calculation
    have s78_4 : LeanBridges.Geometry.line A B = LeanBridges.Geometry.line K B := by
      calc LeanBridges.Geometry.line A B = LeanBridges.Geometry.line Z B := s78_1.symm
        _ = LeanBridges.Geometry.line K B := s78_3
    -- 78.5. substitute line AB = line KB (line 78.4) into line 78.2
    have s78_5 : K ∈ LeanBridges.Geometry.line A B := Eq.subst (motive := (fun t : Set ℂ => K ∈ t)) s78_4.symm s78_2a
    -- 78.6. mun:parallel-off C := H, D := K, X := K, from H5, H7, 1, 78.5
    have s78_6 : ¬ K ∈ LeanBridges.Geometry.line H K := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := A) (B := B) (C := H) (D := K) (X := K) hH5 s1a hH7 s1b s78_5)
    exact s78_6 s6b
  -- 79. substitute Z = B (line 78) into line 23
  have s79 : dist A H = dist K B := Eq.subst (motive := (fun t : ℂ => dist A H = dist K t)) s78 s23a
  -- 80. restate 79
  exact (by (have h := s79; rw [dist_comm K B] at h; exact h) : dist A H = dist B K)

end Parley.Stdlib.Geometry.ParallelEquidistant
