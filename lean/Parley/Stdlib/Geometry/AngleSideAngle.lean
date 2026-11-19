module

public import Geometry
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Parley.Stdlib.Geometry.RayPoint

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AngleSideAngle

theorem angle_side_angle (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (hH7 : LeanBridges.Geometry.Triangle A B C) (hH8 : LeanBridges.Geometry.Triangle D E F) (hH9 : EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) (hH10 : dist A B = dist D E) (hH11 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F) :
    (dist A B = dist D E ∧ dist B C = dist E F ∧ dist C A = dist F D ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F D ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) := by
  -- 1. axi:distance-positive P := A, Q := C, from H7
  have s1 : dist A C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := A) (Q := C) hH7.2.2.1)
  -- 2. obtain G: mun:ray-point A := D, B := F, C := E, r := |AC|, from H8, 1
  obtain ⟨G, s2a, ⟨⟨s2b, s2c⟩, s2d⟩⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := D) (B := F) (C := E) (r := dist A C) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E) s1)
  -- 3. mun:same-side-off-line A := D, B := E, P := G, Q := F, from 2
  have s3 : ¬ G ∈ LeanBridges.Geometry.line D E := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := D) (B := E) (P := G) (Q := F) s2c)
  -- 4. mun:off-line-apart A := D, B := E, P := G, from H8, 3
  have s4a : G ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := D) (B := E) (P := G) hH8.1 s3)
  have s4b : G ≠ E := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := D) (B := E) (P := G) hH8.1 s3)
  -- 5. mun:triangle-off-line P := G, Q := D, R := E, from H8, 3
  have s5 : LeanBridges.Geometry.Triangle G D E := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := D) (R := E) hH8.1 s3)
  -- 6. calculation
  have s6 : EuclideanGeometry.angle B A C = EuclideanGeometry.angle E D G := by
    calc EuclideanGeometry.angle B A C = EuclideanGeometry.angle C A B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := B) (Q := A) (R := C) (Ne.symm hH7.1) (Ne.symm hH7.2.2.1) hH7.2.1)
      _ = EuclideanGeometry.angle F D E := hH9
      _ = EuclideanGeometry.angle E D F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := D) (R := E) (Ne.symm hH8.2.2.1) (Ne.symm hH8.1) (Ne.symm hH8.2.1))
      _ = EuclideanGeometry.angle E D G := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := D) (Q := F) (R := E) (X := G) s2b s2c).symm
  -- 7. restate H10
  have s7 : dist B A = dist E D := by exact (by (have h := hH10; rw [dist_comm A B, dist_comm D E] at h; exact h) : dist B A = dist E D)
  -- 8. restate 2
  have s8 : dist A C = dist D G := by exact s2d.symm
  -- 9. axi:side-angle-side P := B, Q := A, R := C, P′ := E, Q′ := D, R′ := G, from H7, 5, 6, 7, 8
  have s9 : dist B A = dist E D ∧ dist A C = dist D G ∧ dist C B = dist G E ∧ EuclideanGeometry.angle B A C = EuclideanGeometry.angle E D G ∧ EuclideanGeometry.angle A C B = EuclideanGeometry.angle D G E ∧ EuclideanGeometry.angle C B A = EuclideanGeometry.angle G E D := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := B) (P' := E) (Q := A) (Q' := D) (R := C) (R' := G) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_13 G D E] at h; exact h) : LeanBridges.Geometry.Triangle E D G) s7 s6 s8)
  -- 10. calculation
  have s10 : EuclideanGeometry.angle D E F = EuclideanGeometry.angle D E G := by
    calc EuclideanGeometry.angle D E F = EuclideanGeometry.angle A B C := hH11.symm
      _ = EuclideanGeometry.angle C B A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := A) (Q := B) (R := C) hH7.1 (Ne.symm hH7.2.1) hH7.2.2.1)
      _ = EuclideanGeometry.angle G E D := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := B) (P' := E) (Q := A) (Q' := D) (R := C) (R' := G) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_13 G D E] at h; exact h) : LeanBridges.Geometry.Triangle E D G))).mp s9).2
      _ = EuclideanGeometry.angle D E G := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := D) (Q := E) (R := G) hH8.1 s4b (Ne.symm s4a)).symm
  -- 11. mun:on-line-ends A := D, B := E, from H8
  have s11a : D ∈ LeanBridges.Geometry.line D E := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := D) (B := E) hH8.1)
  have s11b : E ∈ LeanBridges.Geometry.line D E := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := D) (B := E) hH8.1)
  -- 12. mun:same-side-of-line A := D, B := E, C := E, P := G, Q := F, from H8, 2, 11
  have s12 : 0 < Complex.im ((G - E) / (D - E)) * Complex.im ((F - E) / (D - E)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := D) (B := E) (C := E) (D := D) (P := G) (Q := F) hH8.1 (Ne.symm hH8.1) s11b s11a s2c)
  -- 13. mun:same-side-same A := E, B := D, P := F, Q := G, R := F, from 12
  have s13 : 0 < Complex.im ((F - E) / (D - E)) * Complex.im ((F - E) / (D - E)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := E) (B := D) (P := F) (Q := G) (R := F) (by (have h := s12; rw [mul_comm (Complex.im ((G - E) / (D - E))) (Complex.im ((F - E) / (D - E)))] at h; exact h) : 0 < Complex.im ((F - E) / (D - E)) * Complex.im ((G - E) / (D - E))) s12)
  -- 14. axi:angle-construction-unique A := E, B := D, C := F, D := F, E := G, from H8, 10, 12, 13
  have s14 : G ∈ LeanBridges.Geometry.ray E F := by exact (Parley.Items.Stdlib.Geometry.axi_angle_construction_unique (E := G) (A := E) (B := D) (C := F) (D := F) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F) s13 s12 s10)
  -- 15. mun:ray-on-line P := G, A := E, B := F, from 14
  have s15 : G ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_ray_on_line (P := G) (A := E) (B := F) s14)
  -- 16. mun:triangle-not-on-line P := D, Q := E, R := F, from H8
  have s16 : ¬ D ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := D) (Q := E) (R := F) hH8)
  -- 17. contradiction
  have s17 : G = F := by
    by_contra (hS1 : G ≠ F)
    -- 17.1. mun:on-line-ends A := E, B := F, from H8
    have s17_1 : F ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := E) (B := F) hH8.2.1)
    -- 17.2. axi:line-uniqueness A := G, B := F, C := E, D := F, from H8, S1, 15, 17.1
    have s17_2 : LeanBridges.Geometry.line G F = LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := G) (B := F) (C := E) (D := F) hS1 hH8.2.1 s15 s17_1)
    -- 17.3. mun:on-line-ends A := D, B := F, from H8
    have s17_3a : D ∈ LeanBridges.Geometry.line D F := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := D) (B := F) hH8.2.2.1)
    have s17_3b : F ∈ LeanBridges.Geometry.line D F := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := D) (B := F) hH8.2.2.1)
    -- 17.4. axi:line-uniqueness A := G, B := F, C := D, D := F, from H8, S1, 2, 17.3
    have s17_4 : LeanBridges.Geometry.line G F = LeanBridges.Geometry.line D F := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := G) (B := F) (C := D) (D := F) hS1 hH8.2.2.1 s2b s17_3b)
    -- 17.5. calculation
    have s17_5 : LeanBridges.Geometry.line D F = LeanBridges.Geometry.line E F := by
      calc LeanBridges.Geometry.line D F = LeanBridges.Geometry.line G F := s17_4.symm
        _ = LeanBridges.Geometry.line E F := s17_2
    -- 17.6. substitute line DF = line EF (line 17.5) into line 17.3
    have s17_6 : D ∈ LeanBridges.Geometry.line E F := Eq.subst (motive := (fun t : Set ℂ => D ∈ t)) s17_5 s17_3a
    exact s16 s17_6
  -- 18. substitute G = F (line 17) into line 9
  have s18 : dist B A = dist E D ∧ dist A C = dist D F ∧ dist C B = dist F E ∧ EuclideanGeometry.angle B A C = EuclideanGeometry.angle E D F ∧ EuclideanGeometry.angle A C B = EuclideanGeometry.angle D F E ∧ EuclideanGeometry.angle C B A = EuclideanGeometry.angle F E D := Eq.subst (motive := (fun t : ℂ => dist B A = dist E D ∧ dist A C = dist D t ∧ dist C B = dist t E ∧ EuclideanGeometry.angle B A C = EuclideanGeometry.angle E D t ∧ EuclideanGeometry.angle A C B = EuclideanGeometry.angle D t E ∧ EuclideanGeometry.angle C B A = EuclideanGeometry.angle t E D)) s17 s9
  -- 19. def:congruent, from H7, H8, 18
  have s19a : dist A C = dist D F := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := B) (P' := E) (Q := A) (Q' := D) (R := C) (R' := F) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F))).mp s18).1.1.1.1.2
  have s19b : dist C B = dist F E := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := B) (P' := E) (Q := A) (Q' := D) (R := C) (R' := F) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F))).mp s18).1.1.1.2
  have s19c : EuclideanGeometry.angle A C B = EuclideanGeometry.angle D F E := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := B) (P' := E) (Q := A) (Q' := D) (R := C) (R' := F) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F))).mp s18).1.2
  -- 20. restate 19
  have s20 : dist B C = dist E F := by exact (by (have h := s19b; rw [dist_comm C B, dist_comm F E] at h; exact h) : dist B C = dist E F)
  -- 21. restate 19
  have s21 : dist C A = dist F D := by exact (by (have h := s19a; rw [dist_comm A C, dist_comm D F] at h; exact h) : dist C A = dist F D)
  -- 22. calculation
  have s22 : EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F D := by
    calc EuclideanGeometry.angle B C A = EuclideanGeometry.angle A C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := B) (Q := C) (R := A) hH7.2.1 hH7.2.2.1 (Ne.symm hH7.1))
      _ = EuclideanGeometry.angle D F E := s19c
      _ = EuclideanGeometry.angle E F D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := D) (Q := F) (R := E) hH8.2.2.1 hH8.2.1 hH8.1)
  -- 23. def:congruent P := A, Q := B, R := C, P′ := D, Q′ := E, R′ := F, from H7, H8, H9, H10, H11, 20, 21, 22
  exact ((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := D) (Q := B) (Q' := E) (R := C) (R' := F) hH7 hH8)).mpr ⟨⟨⟨⟨⟨hH10, s20⟩, s21⟩, hH11⟩, s22⟩, hH9⟩

end Parley.Stdlib.Geometry.AngleSideAngle
