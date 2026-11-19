module

public import Geometry
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.OffLineAlong
public import Parley.Stdlib.Geometry.ParallelEquidistant
public import Parley.Stdlib.Geometry.ParallelOff
public import Parley.Stdlib.Geometry.ParallelSameSide
public import Parley.Stdlib.Geometry.RightAngleAlong

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ParallelHeights

theorem parallel_heights (Q : ℂ) (R : ℂ) (X : ℂ) (Y : ℂ) (H : ℂ) (S : ℂ) (K : ℂ) (T : ℂ) (hH9 : Q ≠ R) (hH10 : X ≠ Y) (hH11 : Complex.im ((R - Q) / (Y - X)) = 0) (hH12 : ¬ Q ∈ LeanBridges.Geometry.line X Y) (hH13 : H ∈ LeanBridges.Geometry.line X Y) (hH14 : S ∈ LeanBridges.Geometry.line X Y) (hH15 : S ≠ H) (hH16 : EuclideanGeometry.angle Q H S = (90 : ℝ) * Real.pi / 180) (hH17 : K ∈ LeanBridges.Geometry.line X Y) (hH18 : T ∈ LeanBridges.Geometry.line X Y) (hH19 : T ≠ K) (hH20 : EuclideanGeometry.angle R K T = (90 : ℝ) * Real.pi / 180) (hH21 : Q ≠ H) (hH22 : Q ≠ S) (hH23 : R ≠ K) (hH24 : R ≠ T) :
    dist Q H = dist R K := by
  -- 1. mun:on-line-ends A := Q, B := R, from H9
  have s1 : R ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := Q) (B := R) hH9)
  -- 2. mun:parallel-off A := Q, B := R, C := X, D := Y, X := R, from H9, H10, H11, H12, 1
  have s2 : ¬ R ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := Q) (B := R) (C := X) (D := Y) (X := R) hH9 hH10 hH11 hH12 s1)
  -- 3. mun:parallel-same-side A := Q, B := R, C := X, D := Y, X := R, from H9, H10, H11, H12, 1
  have s3 : 0 < Complex.im ((R - X) / (Y - X)) * Complex.im ((Q - X) / (Y - X)) := by exact (Parley.Stdlib.Geometry.ParallelSameSide.parallel_same_side (A := Q) (B := R) (C := X) (D := Y) (X := R) hH9 hH10 hH11 hH12 s1 (Ne.symm hH9))
  -- 4. axi:line-uniqueness A := H, B := S, C := X, D := Y, from H10, H13, H14, H15
  have s4 : LeanBridges.Geometry.line H S = LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := H) (B := S) (C := X) (D := Y) (Ne.symm hH15) hH10 hH13 hH14)
  -- 5. axi:line-uniqueness A := K, B := T, C := X, D := Y, from H10, H17, H18, H19
  have s5 : LeanBridges.Geometry.line K T = LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := K) (B := T) (C := X) (D := Y) (Ne.symm hH19) hH10 hH17 hH18)
  -- 6. contradiction
  have s6 : H ≠ K := by
    intro hS1
    -- 6.1. substitute H = K (S1) into H15
    have s6_1 : S ≠ K := Eq.subst (motive := (fun t : ℂ => S ≠ t)) hS1 hH15
    -- 6.2. substitute H = K (S1) into H21
    have s6_2 : K ≠ Q := by apply Ne.symm; (have h := Eq.subst (motive := (fun t : ℂ => Q ≠ t)) hS1 hH21; push_cast at h ⊢; exact_mod_cast h)
    -- 6.3. substitute H = K (S1) into H16
    have s6_3 : EuclideanGeometry.angle Q K S = (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle Q t S = (90 : ℝ) * Real.pi / 180)) hS1 hH16
    -- 6.4. substitute line KT = line XY (line 5) into H14
    have s6_4 : S ∈ LeanBridges.Geometry.line K T := Eq.subst (motive := (fun t : Set ℂ => S ∈ t)) s5.symm hH14
    -- 6.5. mun:same-side-of-line A := X, B := Y, C := K, D := S, P := Q, Q := R, from H10, H14, H17, 3, 6.1
    have s6_5 : 0 < Complex.im ((Q - K) / (S - K)) * Complex.im ((R - K) / (S - K)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := X) (B := Y) (C := K) (D := S) (P := Q) (Q := R) hH10 (Ne.symm s6_1) hH17 hH14 (by (have h := s3; rw [mul_comm (Complex.im ((R - X) / (Y - X))) (Complex.im ((Q - X) / (Y - X)))] at h; exact h) : 0 < Complex.im ((Q - X) / (Y - X)) * Complex.im ((R - X) / (Y - X))))
    -- 6.6. mun:right-angle-along P := R, H := K, S := T, T := S, from H19, H20, H24, 6.4
    have r3898_1 : ¬ R ∈ LeanBridges.Geometry.line K S := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := K) (B := S) (P := Q) (Q := R) s6_5)
    have r3898_2 : LeanBridges.Geometry.Triangle R K S := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := R) (Q := K) (R := S) (Ne.symm s6_1) r3898_1)
    have s6_6 : EuclideanGeometry.angle R K S = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.RightAngleAlong.right_angle_along (P := R) (H := K) (S := T) (T := S) r3898_2.1 hH19 hH20 s6_4 (Ne.symm r3898_2.2.1) hH24 r3898_2)
    -- 6.7. calculation
    have r3904_1 : S ≠ R := by exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := X) (B := Y) (X := S) (Y := R) hH14 s2)
    have s6_7 : EuclideanGeometry.angle S K Q = EuclideanGeometry.angle S K R := by
      calc EuclideanGeometry.angle S K Q = EuclideanGeometry.angle Q K S := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := S) (Q := K) (R := Q) s6_1 (Ne.symm s6_2) (Ne.symm hH22))
        _ = (90 : ℝ) * Real.pi / 180 := s6_3
        _ = EuclideanGeometry.angle R K S := s6_6.symm
        _ = EuclideanGeometry.angle S K R := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := S) (Q := K) (R := R) s6_1 hH23 r3904_1).symm
    -- 6.8. mun:same-side-same A := K, B := S, P := Q, Q := R, R := Q, from 6.5
    have s6_8 : 0 < Complex.im ((Q - K) / (S - K)) * Complex.im ((Q - K) / (S - K)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := K) (B := S) (P := Q) (Q := R) (R := Q) s6_5 (by (have h := s6_5; rw [mul_comm (Complex.im ((Q - K) / (S - K))) (Complex.im ((R - K) / (S - K)))] at h; exact h) : 0 < Complex.im ((R - K) / (S - K)) * Complex.im ((Q - K) / (S - K))))
    -- 6.9. mun:same-side-off-line A := K, B := S, P := Q, Q := R, from 6.5
    have s6_9 : ¬ Q ∈ LeanBridges.Geometry.line K S := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := K) (B := S) (P := Q) (Q := R) s6_5)
    -- 6.10. mun:triangle-off-line P := Q, Q := K, R := S, from 6.1, 6.9
    have s6_10 : LeanBridges.Geometry.Triangle Q K S := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := Q) (Q := K) (R := S) (Ne.symm s6_1) s6_9)
    -- 6.11. axi:angle-construction-unique A := K, B := S, C := Q, D := Q, E := R, from 6.5, 6.7, 6.8, 6.10
    have s6_11 : R ∈ LeanBridges.Geometry.ray K Q := by exact (Parley.Items.Stdlib.Geometry.axi_angle_construction_unique (E := R) (A := K) (B := S) (C := Q) (D := Q) (by (have h := s6_10; rw [LeanBridges.Geometry.triangle_rot_231 Q K S] at h; exact h) : LeanBridges.Geometry.Triangle K S Q) s6_8 (by (have h := s6_5; rw [mul_comm (Complex.im ((Q - K) / (S - K))) (Complex.im ((R - K) / (S - K)))] at h; exact h) : 0 < Complex.im ((R - K) / (S - K)) * Complex.im ((Q - K) / (S - K))) s6_7)
    -- 6.12. mun:ray-on-line P := R, A := K, B := Q, from 6.11
    have s6_12 : R ∈ LeanBridges.Geometry.line K Q := by exact (Parley.Items.Stdlib.Geometry.mun_ray_on_line (P := R) (A := K) (B := Q) s6_11)
    -- 6.13. mun:on-line-ends A := K, B := Q, from 6.2
    have s6_13a : K ∈ LeanBridges.Geometry.line K Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := K) (B := Q) s6_2)
    have s6_13b : Q ∈ LeanBridges.Geometry.line K Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := K) (B := Q) s6_2)
    -- 6.14. axi:line-uniqueness A := Q, B := R, C := K, D := Q, from H9, 6.2, 6.12, 6.13
    have s6_14 : LeanBridges.Geometry.line Q R = LeanBridges.Geometry.line K Q := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := Q) (B := R) (C := K) (D := Q) hH9 s6_2 s6_13b s6_12)
    -- 6.15. substitute line QR = line KQ (line 6.14) into line 6.13
    have s6_15 : K ∈ LeanBridges.Geometry.line Q R := Eq.subst (motive := (fun t : Set ℂ => K ∈ t)) s6_14.symm s6_13a
    -- 6.16. mun:parallel-off A := Q, B := R, C := X, D := Y, X := K, from H9, H10, H11, H12, 6.15
    have s6_16 : ¬ K ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := Q) (B := R) (C := X) (D := Y) (X := K) hH9 hH10 hH11 hH12 s6_15)
    exact s6_16 hH17
  -- 7. axi:line-uniqueness A := H, B := K, C := X, D := Y, from H10, H13, H17, 6
  have s7 : LeanBridges.Geometry.line H K = LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := H) (B := K) (C := X) (D := Y) s6 hH10 hH13 hH17)
  -- 8. substitute line HS = line XY (line 4) into H17
  have s8 : K ∈ LeanBridges.Geometry.line H S := Eq.subst (motive := (fun t : Set ℂ => K ∈ t)) s4.symm hH17
  -- 9. mun:right-angle-along P := Q, T := K, from H16, 8
  have r3950_1 : LeanBridges.Geometry.Triangle Q H S := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := Q) (Q := H) (R := S) hH21 hH15 hH16 hH22)
  have r3950_2 : ¬ Q ∈ LeanBridges.Geometry.line H S := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := Q) (Q := H) (R := S) r3950_1)
  have r3950_3 : ¬ Q ∈ LeanBridges.Geometry.line H K := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := H) (B := S) (X := K) (P := Q) (Ne.symm hH15) s8 (Ne.symm s6) r3950_2)
  have r3950_4 : LeanBridges.Geometry.Triangle Q H K := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := Q) (Q := H) (R := K) s6 r3950_3)
  have s9 : EuclideanGeometry.angle Q H K = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.RightAngleAlong.right_angle_along (P := Q) (H := H) (S := S) (T := K) r3950_1.1 (Ne.symm r3950_1.2.1) hH16 s8 (Ne.symm r3950_4.2.1) r3950_1.2.2.1 r3950_4)
  -- 10. substitute line KT = line XY (line 5) into H13
  have s10 : H ∈ LeanBridges.Geometry.line K T := Eq.subst (motive := (fun t : Set ℂ => H ∈ t)) s5.symm hH13
  -- 11. mun:right-angle-along P := R, H := K, S := T, T := H, from H20, 10
  have r3960_1 : LeanBridges.Geometry.Triangle R K T := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := R) (Q := K) (R := T) hH23 hH19 hH20 hH24)
  have r3960_2 : ¬ R ∈ LeanBridges.Geometry.line K T := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := R) (Q := K) (R := T) r3960_1)
  have r3960_3 : ¬ R ∈ LeanBridges.Geometry.line K H := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := K) (B := T) (X := H) (P := R) (Ne.symm hH19) s10 s6 r3960_2)
  have r3960_4 : LeanBridges.Geometry.Triangle R K H := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := R) (Q := K) (R := H) (Ne.symm s6) r3960_3)
  have s11 : EuclideanGeometry.angle R K H = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.RightAngleAlong.right_angle_along (P := R) (H := K) (S := T) (T := H) r3960_1.1 (Ne.symm r3960_1.2.1) hH20 s10 (Ne.symm r3960_4.2.1) r3960_1.2.2.1 r3960_4)
  -- 12. mun:same-side-of-line A := X, B := Y, C := H, D := K, P := Q, Q := R, from H10, H13, H17, 3, 6
  have s12 : 0 < Complex.im ((Q - H) / (K - H)) * Complex.im ((R - H) / (K - H)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := X) (B := Y) (C := H) (D := K) (P := Q) (Q := R) hH10 s6 hH13 hH17 (by (have h := s3; rw [mul_comm (Complex.im ((R - X) / (Y - X))) (Complex.im ((Q - X) / (Y - X)))] at h; exact h) : 0 < Complex.im ((Q - X) / (Y - X)) * Complex.im ((R - X) / (Y - X))))
  -- 13. contradiction
  have s13 : ¬ (∃ Z ∈ (Set.univ : Set ℂ), Z ∈ LeanBridges.Geometry.line Q R ∧ Z ∈ LeanBridges.Geometry.line H K) := by
    intro hS2
    -- 13.1. obtain Z from S2
    obtain ⟨Z, s13_1a, ⟨s13_1b, s13_1c⟩⟩ := hS2
    -- 13.2. substitute line HK = line XY (line 7) into line 13.1
    have s13_2 : Z ∈ LeanBridges.Geometry.line X Y := Eq.subst (motive := (fun t : Set ℂ => Z ∈ t)) s7 s13_1c
    -- 13.3. mun:parallel-off A := Q, B := R, C := X, D := Y, X := Z, from H9, H10, H11, H12, 13.1
    have s13_3 : ¬ Z ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := Q) (B := R) (C := X) (D := Y) (X := Z) hH9 hH10 hH11 hH12 s13_1b)
    exact s13_3 s13_2
  -- 14. mun:or-right, from 13
  have s14 : LeanBridges.Geometry.line Q R = LeanBridges.Geometry.line H K ∨ ¬ (∃ Z ∈ (Set.univ : Set ℂ), Z ∈ LeanBridges.Geometry.line Q R ∧ Z ∈ LeanBridges.Geometry.line H K) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := LeanBridges.Geometry.line Q R = LeanBridges.Geometry.line H K) (Q := ¬ (∃ Z ∈ (Set.univ : Set ℂ), Z ∈ LeanBridges.Geometry.line Q R ∧ Z ∈ LeanBridges.Geometry.line H K)) s13)
  -- 15. def:parallel A := Q, B := R, C := H, D := K, from H9, 6, 14
  have s15 : Complex.im ((R - Q) / (K - H)) = 0 := ((Parley.Items.Stdlib.Geometry.def_parallel (A := Q) (B := R) (C := H) (D := K) hH9 s6)).mpr s14
  -- 16. thm:parallel-equidistant A := Q, B := R, from H9, 9, 11, 12, 15
  exact (Parley.Stdlib.Geometry.ParallelEquidistant.parallel_equidistant (A := Q) (B := R) (H := H) (K := K) hH9 s12 s15 s9 s11)

end Parley.Stdlib.Geometry.ParallelHeights
