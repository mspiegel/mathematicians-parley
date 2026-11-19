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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/wiedijk/ceva.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ceva.CevianRatio

theorem cevian_ratio (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (O : ℂ) (hH6 : LeanBridges.Geometry.Triangle A B C) (hH7 : Sbtw ℝ B D C) (hH8 : Sbtw ℝ A O D) (hH9 : O ≠ B) (hH10 : O ≠ C) :
    dist D C = dist B D * dist O C * Real.sin (EuclideanGeometry.angle A O C) / (dist O B * Real.sin (EuclideanGeometry.angle B O A)) := by
  -- 1. mun:triangle-on-side P := A, Q := B, R := C, S := D, from H6, H7
  have s1 : LeanBridges.Geometry.Triangle A B D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := A) (Q := B) (R := C) (S := D) hH6 hH7)
  -- 2. mun:triangle-on-side P := A, Q := C, R := B, S := D, from H6, H7
  have s2 : LeanBridges.Geometry.Triangle A C D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := A) (Q := C) (R := B) (S := D) (by (have h := hH6; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) (by (have h := hH7; rw [sbtw_comm (x := B) (y := D) (z := C)] at h; exact h) : Sbtw ℝ C D B))
  -- 3. mun:triangle-on-side P := B, Q := D, R := A, S := O, from H8, 1
  have s3 : LeanBridges.Geometry.Triangle B D O := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := D) (R := A) (S := O) (by (have h := s1; rw [LeanBridges.Geometry.triangle_rot_231 A B D] at h; exact h) : LeanBridges.Geometry.Triangle B D A) (by (have h := hH8; rw [sbtw_comm (x := A) (y := O) (z := D)] at h; exact h) : Sbtw ℝ D O A))
  -- 4. mun:triangle-on-side P := C, Q := D, R := A, S := O, from H8, 2
  have s4 : LeanBridges.Geometry.Triangle C D O := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := C) (Q := D) (R := A) (S := O) (by (have h := s2; rw [LeanBridges.Geometry.triangle_rot_231 A C D] at h; exact h) : LeanBridges.Geometry.Triangle C D A) (by (have h := hH8; rw [sbtw_comm (x := A) (y := O) (z := D)] at h; exact h) : Sbtw ℝ D O A))
  -- 5. mun:triangle-on-side P := B, Q := A, R := D, S := O, from H8, 1
  have s5 : LeanBridges.Geometry.Triangle B A O := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := A) (R := D) (S := O) (by (have h := s1; rw [LeanBridges.Geometry.triangle_swap_12 A B D] at h; exact h) : LeanBridges.Geometry.Triangle B A D) hH8)
  -- 6. thm:law-of-sines P := B, Q := D, R := O, from 3
  have s6 : dist B D * Real.sin (EuclideanGeometry.angle B D O) = dist B O * Real.sin (EuclideanGeometry.angle D O B) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_sines (P := B) (Q := D) (R := O) s3)
  -- 7. thm:law-of-sines P := C, Q := O, R := D, from 4
  have s7 : dist C O * Real.sin (EuclideanGeometry.angle C O D) = dist C D * Real.sin (EuclideanGeometry.angle O D C) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_sines (P := C) (Q := O) (R := D) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_23 C D O] at h; exact h) : LeanBridges.Geometry.Triangle C O D))
  -- 8. axi:supplementary-angles A := B, B := D, D := O, from H7, H10, 3
  have s8 : EuclideanGeometry.angle B D O + EuclideanGeometry.angle O D C = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := B) (B := D) (C := C) (D := O) hH7 (Ne.symm s3.2.1) (Ne.symm s3.2.2.1) hH10)
  -- 9. axi:supplementary-angles A := D, B := O, C := A, D := B, from H8, 1, 3
  have s9 : EuclideanGeometry.angle D O B + EuclideanGeometry.angle B O A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := D) (B := O) (C := A) (D := B) (by (have h := hH8; rw [sbtw_comm (x := A) (y := O) (z := D)] at h; exact h) : Sbtw ℝ D O A) s3.2.2.1 s1.2.1 (Ne.symm s1.1))
  -- 10. axi:supplementary-angles B := O, C := D, D := C, from H8, 2, 4
  have s10 : EuclideanGeometry.angle A O C + EuclideanGeometry.angle C O D = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := A) (B := O) (C := D) (D := C) hH8 s4.2.2.1 (Ne.symm s2.1) s2.2.1)
  -- 11. algebra, from 8
  have s11 : EuclideanGeometry.angle O D C = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle B D O := by linear_combination ((32400) / ((180) * (180))) * s8
  -- 12. calculation
  have s12 : Real.sin (EuclideanGeometry.angle O D C) = Real.sin (EuclideanGeometry.angle B D O) := by
    calc Real.sin (EuclideanGeometry.angle O D C) = Real.sin ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle B D O) := congrArg (fun t : ℝ => Real.sin t) s11
      _ = Real.sin (EuclideanGeometry.angle B D O) := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_supplement (x := EuclideanGeometry.angle B D O))
  -- 13. algebra, from 9
  have s13 : EuclideanGeometry.angle D O B = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle B O A := by linear_combination ((32400) / ((180) * (180))) * s9
  -- 14. calculation
  have s14 : Real.sin (EuclideanGeometry.angle D O B) = Real.sin (EuclideanGeometry.angle B O A) := by
    calc Real.sin (EuclideanGeometry.angle D O B) = Real.sin ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle B O A) := congrArg (fun t : ℝ => Real.sin t) s13
      _ = Real.sin (EuclideanGeometry.angle B O A) := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_supplement (x := EuclideanGeometry.angle B O A))
  -- 15. algebra, from 10
  have s15 : EuclideanGeometry.angle C O D = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A O C := by linear_combination ((32400) / ((180) * (180))) * s10
  -- 16. calculation
  have s16 : Real.sin (EuclideanGeometry.angle C O D) = Real.sin (EuclideanGeometry.angle A O C) := by
    calc Real.sin (EuclideanGeometry.angle C O D) = Real.sin ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A O C) := congrArg (fun t : ℝ => Real.sin t) s15
      _ = Real.sin (EuclideanGeometry.angle A O C) := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_supplement (x := EuclideanGeometry.angle A O C))
  -- 17. substitute sin(∠DOB) = sin(∠BOA) (line 14) into line 6
  have s17 : dist B D * Real.sin (EuclideanGeometry.angle B D O) = dist B O * Real.sin (EuclideanGeometry.angle B O A) := Eq.subst (motive := (fun t : ℝ => dist B D * Real.sin (EuclideanGeometry.angle B D O) = dist B O * t)) s14 s6
  -- 18. substitute sin(∠COD) = sin(∠AOC) (line 16) into line 7
  have s18 : dist C O * Real.sin (EuclideanGeometry.angle A O C) = dist C D * Real.sin (EuclideanGeometry.angle O D C) := Eq.subst (motive := (fun t : ℝ => dist C O * t = dist C D * Real.sin (EuclideanGeometry.angle O D C))) s16 s7
  -- 19. substitute sin(∠ODC) = sin(∠BDO) (line 12) into line 18
  have s19 : dist C O * Real.sin (EuclideanGeometry.angle A O C) = dist C D * Real.sin (EuclideanGeometry.angle B D O) := Eq.subst (motive := (fun t : ℝ => dist C O * Real.sin (EuclideanGeometry.angle A O C) = dist C D * t)) s12 s18
  -- 20. axi:distance-positive P := O, Q := B, from 3
  have s20 : dist O B > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := O) (Q := B) (Ne.symm s3.2.2.1))
  -- 21. mun:sine-positive P := B, Q := O, R := A, from 5
  have s21 : Real.sin (EuclideanGeometry.angle B O A) > 0 := by exact (Parley.Items.Stdlib.Geometry.mun_sine_positive (P := B) (Q := O) (R := A) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_23 B A O] at h; exact h) : LeanBridges.Geometry.Triangle B O A))
  -- 22. calculation
  have r98_1 : dist O B ≠ 0 := ne_of_gt (by linarith only [s20])
  have r98_2 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := ne_of_gt (by linarith only [s21])
  calc dist D C = dist B D * dist D C * Real.sin (EuclideanGeometry.angle B D O) / (dist O B * Real.sin (EuclideanGeometry.angle B O A)) := by
        rw [dist_comm D C, dist_comm O B]
        exact (by have hz1 : dist B O ≠ 0 := (by (have h := r98_1; rw [dist_comm O B] at h; exact h) : dist B O ≠ 0); have hz2 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := r98_2; linear_combination (norm := (field)) ((-dist C D) / ((dist B O * Real.sin (EuclideanGeometry.angle B O A)))) * s17)
    _ = dist B D * dist O C * Real.sin (EuclideanGeometry.angle A O C) / (dist O B * Real.sin (EuclideanGeometry.angle B O A)) := by
        rw [dist_comm O B, dist_comm D C, dist_comm O C]
        exact (by have hz1 : dist B O ≠ 0 := (by (have h := r98_1; rw [dist_comm O B] at h; exact h) : dist B O ≠ 0); have hz2 : Real.sin (EuclideanGeometry.angle B O A) ≠ 0 := r98_2; linear_combination (norm := (field)) ((-dist B D) / ((dist B O * Real.sin (EuclideanGeometry.angle B O A)))) * s19)

end Parley.Proofs.Wiedijk.Ceva.CevianRatio
