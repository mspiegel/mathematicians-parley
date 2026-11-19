module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
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
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
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
public import Mathlib.Tactic.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Wiedijk.Ceva.CevianRatio

/-! Written from proofs/wiedijk/ceva.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ceva.Ceva

theorem ceva (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (O : ℂ) (hH8 : LeanBridges.Geometry.Triangle A B C) (hH9 : Sbtw ℝ B D C) (hH10 : Sbtw ℝ C E A) (hH11 : Sbtw ℝ A F B) (hH12 : Sbtw ℝ A O D) (hH13 : Sbtw ℝ B O E) (hH14 : Sbtw ℝ C O F) :
    dist A F * dist B D * dist C E = dist F B * dist D C * dist E A := by
  set x : ℝ := dist O C * Real.sin (EuclideanGeometry.angle A O C) / (dist O B * Real.sin (EuclideanGeometry.angle B O A)) with hD1
  set y : ℝ := dist O A * Real.sin (EuclideanGeometry.angle B O A) / (dist O C * Real.sin (EuclideanGeometry.angle C O B)) with hD2
  set z : ℝ := dist O B * Real.sin (EuclideanGeometry.angle C O B) / (dist O A * Real.sin (EuclideanGeometry.angle A O C)) with hD3
  -- 1. thm:cevian-ratio, from H8, H9, H12
  have r135_1 : B ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := O) (S := B) (T := E) hH13)
  have r135_2 : C ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := O) (S := C) (T := F) hH14)
  have s1 : dist D C = dist B D * dist O C * Real.sin (EuclideanGeometry.angle A O C) / (dist O B * Real.sin (EuclideanGeometry.angle B O A)) := by exact (Parley.Proofs.Wiedijk.Ceva.CevianRatio.cevian_ratio (A := A) (B := B) (C := C) (D := D) (O := O) hH8 hH9 hH12 (Ne.symm r135_1) (Ne.symm r135_2))
  -- 2. thm:cevian-ratio A := B, B := C, C := A, D := E, from H8, H10, H13
  have r140_1 : C ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := O) (S := C) (T := F) hH14)
  have r140_2 : A ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := O) (S := A) (T := D) hH12)
  have s2 : dist E A = dist C E * dist O A * Real.sin (EuclideanGeometry.angle B O A) / (dist O C * Real.sin (EuclideanGeometry.angle C O B)) := by exact (Parley.Proofs.Wiedijk.Ceva.CevianRatio.cevian_ratio (A := B) (B := C) (C := A) (D := E) (O := O) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) hH10 hH13 (Ne.symm r140_1) (Ne.symm r140_2))
  -- 3. thm:cevian-ratio A := C, B := A, C := B, D := F, from H8, H11, H14
  have r145_1 : A ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := O) (S := A) (T := D) hH12)
  have r145_2 : B ≠ O := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := O) (S := B) (T := E) hH13)
  have s3 : dist F B = dist A F * dist O B * Real.sin (EuclideanGeometry.angle C O B) / (dist O A * Real.sin (EuclideanGeometry.angle A O C)) := by exact (Parley.Proofs.Wiedijk.Ceva.CevianRatio.cevian_ratio (A := C) (B := A) (C := B) (D := F) (O := O) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B) hH11 hH14 (Ne.symm r145_1) (Ne.symm r145_2))
  -- 4. mun:triangle-on-side P := A, Q := B, R := C, S := D, from H8, H9
  have s4 : LeanBridges.Geometry.Triangle A B D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := A) (Q := B) (R := C) (S := D) hH8 hH9)
  -- 5. mun:triangle-on-side P := B, Q := A, R := D, S := O, from H12, 4
  have s5 : LeanBridges.Geometry.Triangle B A O := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := A) (R := D) (S := O) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_12 A B D] at h; exact h) : LeanBridges.Geometry.Triangle B A D) hH12)
  -- 6. mun:triangle-on-side P := B, Q := C, R := A, S := E, from H8, H10
  have s6 : LeanBridges.Geometry.Triangle B C E := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := C) (R := A) (S := E) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) hH10)
  -- 7. mun:triangle-on-side P := C, Q := B, R := E, S := O, from H13, 6
  have s7 : LeanBridges.Geometry.Triangle C B O := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := C) (Q := B) (R := E) (S := O) (by (have h := s6; rw [LeanBridges.Geometry.triangle_swap_12 B C E] at h; exact h) : LeanBridges.Geometry.Triangle C B E) hH13)
  -- 8. mun:triangle-on-side P := C, Q := A, R := B, S := F, from H8, H11
  have s8 : LeanBridges.Geometry.Triangle C A F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := C) (Q := A) (R := B) (S := F) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B) hH11)
  -- 9. mun:triangle-on-side P := A, Q := C, R := F, S := O, from H14, 8
  have s9 : LeanBridges.Geometry.Triangle A C O := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := A) (Q := C) (R := F) (S := O) (by (have h := s8; rw [LeanBridges.Geometry.triangle_swap_12 C A F] at h; exact h) : LeanBridges.Geometry.Triangle A C F) hH14)
  -- 10. mun:sine-positive P := B, Q := O, R := A, from 5
  have s10 : Real.sin (EuclideanGeometry.angle B O A) > 0 := by exact (Parley.Items.Stdlib.Geometry.mun_sine_positive (P := B) (Q := O) (R := A) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_23 B A O] at h; exact h) : LeanBridges.Geometry.Triangle B O A))
  -- 11. mun:sine-positive P := C, Q := O, R := B, from 7
  have s11 : Real.sin (EuclideanGeometry.angle C O B) > 0 := by exact (Parley.Items.Stdlib.Geometry.mun_sine_positive (P := C) (Q := O) (R := B) (by (have h := s7; rw [LeanBridges.Geometry.triangle_swap_23 C B O] at h; exact h) : LeanBridges.Geometry.Triangle C O B))
  -- 12. mun:sine-positive P := A, Q := O, R := C, from 9
  have s12 : Real.sin (EuclideanGeometry.angle A O C) > 0 := by exact (Parley.Items.Stdlib.Geometry.mun_sine_positive (P := A) (Q := O) (R := C) (by (have h := s9; rw [LeanBridges.Geometry.triangle_swap_23 A C O] at h; exact h) : LeanBridges.Geometry.Triangle A O C))
  -- 13. axi:distance-positive P := O, Q := A, from 5
  have s13 : dist O A > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := O) (Q := A) (Ne.symm s5.2.1))
  -- 14. axi:distance-positive P := O, Q := B, from 5
  have s14 : dist O B > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := O) (Q := B) (Ne.symm s5.2.2.1))
  -- 15. axi:distance-positive P := O, Q := C, from 7
  have s15 : dist O C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := O) (Q := C) (Ne.symm s7.2.2.1))
  -- 16. membership, from D1
  have r186_1 : dist O B ≠ 0 := ne_of_gt (by linarith only [s14])
  have r186_2 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := ne_of_gt (by linarith only [s10])
  -- 17. membership, from D2
  have r191_1 : dist O C ≠ 0 := ne_of_gt (by linarith only [s15])
  have r191_2 : Real.sin (EuclideanGeometry.angle C O B) ≠ 0 := ne_of_gt (by linarith only [s11])
  -- 18. membership, from D3
  have r196_1 : dist O A ≠ 0 := ne_of_gt (by linarith only [s13])
  have r196_2 : Real.sin (EuclideanGeometry.angle A O C) ≠ 0 := ne_of_gt (by linarith only [s12])
  -- 19. algebra, from D1, 1
  have r201_1 : dist O B ≠ 0 := ne_of_gt (by linarith only [s14])
  have r201_2 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := ne_of_gt (by linarith only [s10])
  have s19 : dist D C = dist B D * x := by
    simp only [hD1] at ⊢
    have hz1 : dist O B ≠ 0 := r201_1; have hz2 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := r201_2; linear_combination (norm := (field)) s1
  -- 20. algebra, from D2, 2
  have r206_1 : dist O C ≠ 0 := ne_of_gt (by linarith only [s15])
  have r206_2 : Real.sin (EuclideanGeometry.angle C O B) ≠ 0 := ne_of_gt (by linarith only [s11])
  have s20 : dist E A = dist C E * y := by
    simp only [hD2] at ⊢
    have hz1 : dist O C ≠ 0 := r206_1; have hz2 : Real.sin (EuclideanGeometry.angle C O B) ≠ 0 := r206_2; linear_combination (norm := (field)) s2
  -- 21. algebra, from D3, 3
  have r211_1 : dist O A ≠ 0 := ne_of_gt (by linarith only [s13])
  have r211_2 : Real.sin (EuclideanGeometry.angle A O C) ≠ 0 := ne_of_gt (by linarith only [s12])
  have s21 : dist F B = dist A F * z := by
    simp only [hD3] at ⊢
    have hz1 : dist O A ≠ 0 := r211_1; have hz2 : Real.sin (EuclideanGeometry.angle A O C) ≠ 0 := r211_2; linear_combination (norm := (field)) s3
  -- 22. algebra, from D1, D2, D3
  have r216_1 : dist O A ≠ 0 := ne_of_gt (by linarith only [s13])
  have r216_2 : dist O B ≠ 0 := ne_of_gt (by linarith only [s14])
  have r216_3 : dist O C ≠ 0 := ne_of_gt (by linarith only [s15])
  have r216_4 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := ne_of_gt (by linarith only [s10])
  have r216_5 : Real.sin (EuclideanGeometry.angle C O B) ≠ 0 := ne_of_gt (by linarith only [s11])
  have r216_6 : Real.sin (EuclideanGeometry.angle A O C) ≠ 0 := ne_of_gt (by linarith only [s12])
  have s22 : x * y * z = 1 := by
    simp only [hD1, hD2, hD3] at ⊢
    have hz1 : dist O B ≠ 0 := r216_2; have hz2 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := r216_4; have hz3 : dist O C ≠ 0 := r216_3; have hz4 : Real.sin (EuclideanGeometry.angle C O B) ≠ 0 := r216_5; have hz5 : dist O A ≠ 0 := r216_1; have hz6 : Real.sin (EuclideanGeometry.angle A O C) ≠ 0 := r216_6; field
  -- 23. calculation
  calc dist A F * dist B D * dist C E = dist A F * z * (dist B D * x) * (dist C E * y) := by linear_combination (-(dist A F * dist B D * dist C E)) * s22
    _ = dist A F * z * (dist B D * x) * dist E A := congrArg (fun t : ℝ => dist A F * z * (dist B D * x) * t) s20.symm
    _ = dist A F * z * dist D C * dist E A := congrArg (fun t : ℝ => dist A F * z * t * dist E A) s19.symm
    _ = dist F B * dist D C * dist E A := congrArg (fun t : ℝ => t * dist D C * dist E A) s21.symm

end Parley.Proofs.Wiedijk.Ceva.Ceva
