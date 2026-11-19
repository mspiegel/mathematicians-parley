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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.AlternateAnglesConverse

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ParallelThrough

theorem parallel_through (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    (∃ D ∈ (Set.univ : Set ℂ), ∃ E ∈ (Set.univ : Set ℂ), ((((Complex.im ((D - R) / (Q - P)) = 0 ∧ Complex.im ((E - R) / (P - Q)) = 0) ∧ Sbtw ℝ D R E) ∧ Complex.im ((D - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0) ∧ Complex.im ((E - R) / (Q - R)) * Complex.im ((P - R) / (Q - R)) < 0) ∧ 0 < Complex.im ((P - R) / (D - R)) * Complex.im ((Q - R) / (D - R))) := by
  -- 1. axi:distance-positive P := Q, Q := R, from H4
  have s1 : dist Q R > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := Q) (Q := R) hH4.2.1)
  -- 2. obtain Q′: mun:segment-extension A := Q, B := R, r := |QR|, from H4, 1
  obtain ⟨Q', s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := Q) (B := R) (r := dist Q R) hH4.2.1 s1)
  -- 3. mun:triangle-not-on-line P := Q, Q := R, R := P, from H4
  have s3 : ¬ Q ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := Q) (Q := R) (R := P) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q R P))
  -- 4. mun:on-line-ends A := R, B := P, from H4
  have s4a : R ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := R) (B := P) (Ne.symm hH4.2.2.1))
  have s4b : P ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := R) (B := P) (Ne.symm hH4.2.2.1))
  -- 5. mun:segment-across-line A := R, B := P, P := Q, Q := Q′, M := R, from H4, 2, 3, 4
  have s5 : Complex.im ((Q - R) / (P - R)) * Complex.im ((Q' - R) / (P - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := R) (B := P) (M := R) (P := Q) (Q := Q') (Ne.symm hH4.2.2.1) s4a s3 s2b)
  -- 6. mun:opposite-sides-off-line A := R, B := P, P := Q, Q := Q′, from 5
  have s6 : ¬ Q' ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := R) (B := P) (P := Q) (Q := Q') s5)
  -- 7. mun:triangle-off-line P := Q′, Q := R, R := P, from H4, 6
  have s7 : LeanBridges.Geometry.Triangle Q' R P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := Q') (Q := R) (R := P) (Ne.symm hH4.2.2.1) s6)
  -- 8. axi:angle-measure P := R, Q := P, R := Q, from H4
  have s8a : EuclideanGeometry.angle R P Q > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := R) (Q := P) (R := Q) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  have s8b : EuclideanGeometry.angle R P Q < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := R) (Q := P) (R := Q) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  -- 9. obtain D: axi:angle-construction A := R, B := P, C := Q′, x := ∠RPQ, from 7, 8
  obtain ⟨D, s9a, ⟨s9b, s9c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_angle_construction (A := R) (B := P) (C := Q') (x := EuclideanGeometry.angle R P Q) (by (have h := s7; rw [LeanBridges.Geometry.triangle_rot_231 Q' R P] at h; exact h) : LeanBridges.Geometry.Triangle R P Q') s8a s8b)
  -- 10. mun:same-opposite-opposite A := R, B := P, P := D, Q := Q′, R := Q, from 5, 9
  have s10 : Complex.im ((D - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := R) (B := P) (P := D) (Q := Q') (R := Q) s9b (by (have h := s5; rw [mul_comm (Complex.im ((Q - R) / (P - R))) (Complex.im ((Q' - R) / (P - R)))] at h; exact h) : Complex.im ((Q' - R) / (P - R)) * Complex.im ((Q - R) / (P - R)) < 0))
  -- 11. mun:opposite-sides-off-line A := R, B := P, P := D, from 10
  have s11 : ¬ D ∈ LeanBridges.Geometry.line R P := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_2 (A := R) (B := P) (P := D) (Q := Q) s10)
  -- 12. mun:off-line-apart A := R, B := P, P := D, from H4, 11
  have s12a : D ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := R) (B := P) (P := D) (Ne.symm hH4.2.2.1) s11)
  have s12b : D ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := R) (B := P) (P := D) (Ne.symm hH4.2.2.1) s11)
  -- 13. calculation
  have s13 : EuclideanGeometry.angle D R P = EuclideanGeometry.angle R P Q := by
    calc EuclideanGeometry.angle D R P = EuclideanGeometry.angle P R D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := D) (Q := R) (R := P) s12a hH4.2.2.1 s12b)
      _ = EuclideanGeometry.angle R P Q := s9c
  -- 14. thm:alternate-angles-converse S := D, from H4, 10, 13
  have s14 : Complex.im ((D - R) / (Q - P)) = 0 := by exact (Parley.Stdlib.Geometry.AlternateAnglesConverse.alternate_angles_converse (P := P) (Q := Q) (R := R) (S := D) hH4 s10 s13)
  -- 15. axi:distance-positive P := D, Q := R, from 12
  have s15 : dist D R > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := D) (Q := R) s12a)
  -- 16. obtain E: mun:segment-extension A := D, B := R, r := |DR|, from 12, 15
  obtain ⟨E, s16a, ⟨s16b, s16c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := D) (B := R) (r := dist D R) s12a s15)
  -- 17. mun:between-collinear S := D, T := E, from 16
  have s17 : Collinear ℝ {E, R, D} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := R) (S := D) (T := E) s16b)
  -- 18. def:on-line P := E, A := R, B := D, from 12, 17
  have s18 : E ∈ LeanBridges.Geometry.line R D := ((Parley.Items.Stdlib.Geometry.def_on_line (A := R) (B := D) (P := E) (Ne.symm s12a))).mpr (by (have h := s17; rw [LeanBridges.Geometry.collinear_rot_231 E R D] at h; exact h) : Collinear ℝ {R, D, E})
  -- 19. mun:between-apart S := D, T := E, from 16
  have s19a : D ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := R) (S := D) (T := E) s16b)
  have s19b : E ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := R) (S := D) (T := E) s16b)
  -- 20. mun:parallel-along A := R, B := D, C := P, D := Q, from 14, 18, 19
  have s20 : Complex.im ((E - R) / (P - Q)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := R) (B := D) (C := P) (D := Q) (E := E) s14 (Ne.symm s19a) s18 s19b)
  -- 21. mun:triangle-not-on-line P := R, Q := P, R := Q, from H4
  have s21 : ¬ R ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := R) (Q := P) (R := Q) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  -- 22. def:parallel A := R, B := D, C := P, D := Q, from H4, 12, 14
  have s22 : LeanBridges.Geometry.line R D = LeanBridges.Geometry.line P Q ∨ ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R D ∧ X ∈ LeanBridges.Geometry.line P Q) := by exact ((Parley.Items.Stdlib.Geometry.def_parallel (A := R) (B := D) (C := P) (D := Q) (Ne.symm s12a) hH4.1)).mp s14
  -- 23. mun:on-line-ends A := R, B := D, from 12
  have s23 : R ∈ LeanBridges.Geometry.line R D := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := R) (B := D) (Ne.symm s12a))
  -- 24. contradiction
  have s24 : ¬ LeanBridges.Geometry.line R D = LeanBridges.Geometry.line P Q := by
    intro hS1
    -- 24.1. substitute line RD = line PQ (S1) into line 23
    have s24_1 : R ∈ LeanBridges.Geometry.line P Q := Eq.subst (motive := (fun t : Set ℂ => R ∈ t)) hS1 s23
    exact s21 s24_1
  -- 25. mun:disjunctive-syllogism-left, from 22, 24
  have s25 : ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R D ∧ X ∈ LeanBridges.Geometry.line P Q) := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := LeanBridges.Geometry.line R D = LeanBridges.Geometry.line P Q) (Q := ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R D ∧ X ∈ LeanBridges.Geometry.line P Q)) s22 s24)
  -- 26. mun:on-line-ends A := P, B := Q, from H4
  have s26a : P ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := P) (B := Q) hH4.1)
  have s26b : Q ∈ LeanBridges.Geometry.line P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := P) (B := Q) hH4.1)
  -- 27. contradiction
  have s27 : ¬ P ∈ LeanBridges.Geometry.line R D := by
    intro hS2
    -- 27.1. exhibit, from S2, 26
    have s27_1 : ∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R D ∧ X ∈ LeanBridges.Geometry.line P Q := ⟨P, Set.mem_univ _, ⟨hS2, s26a⟩⟩
    exact s25 s27_1
  -- 28. contradiction
  have s28 : ¬ Q ∈ LeanBridges.Geometry.line R D := by
    intro hS3
    -- 28.1. exhibit, from S3, 26
    have s28_1 : ∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R D ∧ X ∈ LeanBridges.Geometry.line P Q := ⟨Q, Set.mem_univ _, ⟨hS3, s26b⟩⟩
    exact s25 s28_1
  -- 29. axi:plane-separation A := R, B := D, from 12, 27, 28
  have s29 : 0 < Complex.im ((P - R) / (D - R)) * Complex.im ((Q - R) / (D - R)) ∨ Complex.im ((P - R) / (D - R)) * Complex.im ((Q - R) / (D - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.axi_plane_separation (A := R) (B := D) (P := P) (Q := Q) (Ne.symm s12a) s27 s28)
  -- 30. contradiction
  have s30 : ¬ Complex.im ((P - R) / (D - R)) * Complex.im ((Q - R) / (D - R)) < 0 := by
    intro hS4
    -- 30.1. obtain X: axi:plane-separation-crossing A := R, B := D, from S4, 12
    obtain ⟨X, s30_1a, ⟨s30_1b, s30_1c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := R) (B := D) (P := P) (Q := Q) (Ne.symm s12a) hS4)
    -- 30.2. mun:between-collinear R := X, S := P, T := Q, from 30.1
    have s30_2 : Collinear ℝ {Q, X, P} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := X) (S := P) (T := Q) s30_1c)
    -- 30.3. def:on-line P := X, A := P, B := Q, from H4, 30.2
    have s30_3 : X ∈ LeanBridges.Geometry.line P Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := P) (B := Q) (P := X) hH4.1)).mpr (by (have h := s30_2; rw [LeanBridges.Geometry.collinear_rot_312 Q X P] at h; exact h) : Collinear ℝ {P, Q, X})
    -- 30.4. exhibit, from 30.1, 30.3
    have s30_4 : ∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line R D ∧ X ∈ LeanBridges.Geometry.line P Q := ⟨X, Set.mem_univ _, ⟨s30_1b, s30_3⟩⟩
    exact s25 s30_4
  -- 31. mun:disjunctive-syllogism, from 29, 30
  have s31 : 0 < Complex.im ((P - R) / (D - R)) * Complex.im ((Q - R) / (D - R)) := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := 0 < Complex.im ((P - R) / (D - R)) * Complex.im ((Q - R) / (D - R))) (Q := Complex.im ((P - R) / (D - R)) * Complex.im ((Q - R) / (D - R)) < 0) s29 s30)
  -- 32. mun:segment-across-line A := R, B := D, P := Q, Q := Q′, M := R, from 2, 12, 23, 28
  have s32 : Complex.im ((Q - R) / (D - R)) * Complex.im ((Q' - R) / (D - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := R) (B := D) (M := R) (P := Q) (Q := Q') (Ne.symm s12a) s23 s28 s2b)
  -- 33. mun:same-opposite-opposite A := R, B := D, R := Q′, from 31, 32
  have s33 : Complex.im ((P - R) / (D - R)) * Complex.im ((Q' - R) / (D - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := R) (B := D) (P := P) (Q := Q) (R := Q') s31 s32)
  -- 34. mun:opposite-sides-off-line A := R, B := D, Q := Q′, from 33
  have s34 : ¬ Q' ∈ LeanBridges.Geometry.line R D := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := R) (B := D) (P := P) (Q := Q') s33)
  -- 35. mun:off-line-swap P := D, Q := Q′, from 12, 34
  have s35 : ¬ D ∈ LeanBridges.Geometry.line R Q' := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := D) (Q := Q') (R := R) (Ne.symm s12a) s34)
  -- 36. obtain Y: axi:plane-separation-crossing A := R, B := D, Q := Q′, from 12, 33
  obtain ⟨Y, s36a, ⟨s36b, s36c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := R) (B := D) (P := P) (Q := Q') (Ne.symm s12a) s33)
  -- 37. mun:segment-off-line A := R, B := P, P := Q′, Q := P, X := Y, from H4, 4, 6, 36
  have s37 : 0 < Complex.im ((Y - R) / (P - R)) * Complex.im ((Q' - R) / (P - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := R) (B := P) (P := Q') (Q := P) (X := Y) (Ne.symm hH4.2.2.1) s4b s6 (by (have h := s36c; rw [sbtw_comm (x := P) (y := Y) (z := Q')] at h; exact h) : Sbtw ℝ Q' Y P))
  -- 38. mun:same-side-same A := R, B := P, P := Y, Q := Q′, R := D, from 9, 37
  have s38 : 0 < Complex.im ((Y - R) / (P - R)) * Complex.im ((D - R) / (P - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := R) (B := P) (P := Y) (Q := Q') (R := D) s37 (by (have h := s9b; rw [mul_comm (Complex.im ((D - R) / (P - R))) (Complex.im ((Q' - R) / (P - R)))] at h; exact h) : 0 < Complex.im ((Q' - R) / (P - R)) * Complex.im ((D - R) / (P - R))))
  -- 39. mun:between-apart S := Q, T := Q′, from 2
  have s39a : Q ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := R) (S := Q) (T := Q') s2b)
  have s39b : Q' ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := R) (S := Q) (T := Q') s2b)
  -- 40. mun:ray-side-transfer P := D, S := P, Q := Q′, X := Y, from 35, 36, 38, 39
  have s40 : 0 < Complex.im ((Y - R) / (Q' - R)) * Complex.im ((D - R) / (Q' - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_ray_side_transfer (P := D) (Q := Q') (R := R) (S := P) (X := Y) s36b s38 (Ne.symm s39b) s35)
  -- 41. mun:on-line-ends A := R, B := Q′, from 39
  have s41a : R ∈ LeanBridges.Geometry.line R Q' := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := R) (B := Q') (Ne.symm s39b))
  have s41b : Q' ∈ LeanBridges.Geometry.line R Q' := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := R) (B := Q') (Ne.symm s39b))
  -- 42. mun:off-line-swap Q := Q′, from H4, 6
  have s42 : ¬ P ∈ LeanBridges.Geometry.line R Q' := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_swap (P := P) (Q := Q') (R := R) (Ne.symm hH4.2.2.1) s6)
  -- 43. mun:segment-off-line A := R, B := Q′, Q := Q′, X := Y, from 36, 39, 41, 42
  have s43 : 0 < Complex.im ((Y - R) / (Q' - R)) * Complex.im ((P - R) / (Q' - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := R) (B := Q') (P := P) (Q := Q') (X := Y) (Ne.symm s39b) s41b s42 s36c)
  -- 44. mun:same-side-same A := R, B := Q′, P := D, Q := Y, R := P, from 40, 43
  have s44 : 0 < Complex.im ((D - R) / (Q' - R)) * Complex.im ((P - R) / (Q' - R)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := R) (B := Q') (P := D) (Q := Y) (R := P) (by (have h := s40; rw [mul_comm (Complex.im ((Y - R) / (Q' - R))) (Complex.im ((D - R) / (Q' - R)))] at h; exact h) : 0 < Complex.im ((D - R) / (Q' - R)) * Complex.im ((Y - R) / (Q' - R))) s43)
  -- 45. mun:segment-across-line A := R, B := Q′, P := D, Q := E, M := R, from 16, 35, 39, 41
  have s45 : Complex.im ((D - R) / (Q' - R)) * Complex.im ((E - R) / (Q' - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := R) (B := Q') (M := R) (P := D) (Q := E) (Ne.symm s39b) s41a s35 s16b)
  -- 46. mun:same-opposite-opposite A := R, B := Q′, Q := D, R := E, from 44, 45
  have s46 : Complex.im ((P - R) / (Q' - R)) * Complex.im ((E - R) / (Q' - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := R) (B := Q') (P := P) (Q := D) (R := E) (by (have h := s44; rw [mul_comm (Complex.im ((D - R) / (Q' - R))) (Complex.im ((P - R) / (Q' - R)))] at h; exact h) : 0 < Complex.im ((P - R) / (Q' - R)) * Complex.im ((D - R) / (Q' - R))) s45)
  -- 47. mun:between-collinear S := Q, T := Q′, from 2
  have s47 : Collinear ℝ {Q', R, Q} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := R) (S := Q) (T := Q') s2b)
  -- 48. def:on-line P := Q, A := R, B := Q′, from 39, 47
  have s48 : Q ∈ LeanBridges.Geometry.line R Q' := ((Parley.Items.Stdlib.Geometry.def_on_line (A := R) (B := Q') (P := Q) (Ne.symm s39b))).mpr (by (have h := s47; rw [LeanBridges.Geometry.collinear_swap_12 Q' R Q] at h; exact h) : Collinear ℝ {R, Q', Q})
  -- 49. mun:opposite-sides-of-line A := R, B := Q′, C := R, D := Q, Q := E, from 39, 41, 46, 48
  have s49 : Complex.im ((P - R) / (Q - R)) * Complex.im ((E - R) / (Q - R)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_of_line (A := R) (B := Q') (C := R) (D := Q) (P := P) (Q := E) (Ne.symm s39b) (Ne.symm s39a) s41a s48 s46)
  -- 50. exhibit, from 10, 14, 16, 20, 31, 49
  exact ⟨D, Set.mem_univ _, E, Set.mem_univ _, ⟨⟨⟨⟨⟨s14, s20⟩, s16b⟩, s10⟩, (by (have h := s49; rw [mul_comm (Complex.im ((P - R) / (Q - R))) (Complex.im ((E - R) / (Q - R)))] at h; exact h) : Complex.im ((E - R) / (Q - R)) * Complex.im ((P - R) / (Q - R)) < 0)⟩, s31⟩⟩

end Parley.Stdlib.Geometry.ParallelThrough
