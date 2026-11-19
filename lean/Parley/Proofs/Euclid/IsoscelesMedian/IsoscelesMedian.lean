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

/-! Written from proofs/euclid/isosceles-median.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.IsoscelesMedian.IsoscelesMedian

theorem isosceles_median (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : dist A B = dist A C) (hH7 : Sbtw ℝ B M C ∧ dist B M = dist M C) (hH8 : LeanBridges.Geometry.Triangle A M B) (hH9 : LeanBridges.Geometry.Triangle M A C) :
    EuclideanGeometry.angle A M B = (90 : ℝ) * Real.pi / 180 ∧ EuclideanGeometry.angle B A M = EuclideanGeometry.angle M A C := by
  -- 1. def:midpoint A := B, B := C, from H7
  have s1a : Sbtw ℝ B M C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := B) (B := C) (M := M))).mp hH7).1
  have s1b : dist B M = dist M C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := B) (B := C) (M := M))).mp hH7).2
  -- 2. restate 1
  have s2 : dist B M = dist C M := by exact (by (have h := s1b; rw [dist_comm M C] at h; exact h) : dist B M = dist C M)
  -- 3. thm:side-side-side C := M, D := A, E := C, F := M, from H6, H8, H9, 2
  have s3 : dist A B = dist A C ∧ dist B M = dist C M ∧ dist M A = dist M A ∧ EuclideanGeometry.angle A B M = EuclideanGeometry.angle A C M ∧ EuclideanGeometry.angle B M A = EuclideanGeometry.angle C M A ∧ EuclideanGeometry.angle M A B = EuclideanGeometry.angle M A C := by exact (Parley.Stdlib.Geometry.SideSideSide.side_side_side (A := A) (B := B) (C := M) (D := A) (E := C) (F := M) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_23 A M B] at h; exact h) : LeanBridges.Geometry.Triangle A B M) (by (have h := hH9; rw [LeanBridges.Geometry.triangle_rot_231 M A C] at h; exact h) : LeanBridges.Geometry.Triangle A C M) hH6 s2 rfl)
  -- 4. def:congruent P := A, Q := B, R := M, P′ := A, Q′ := C, R′ := M, from H8, H9, 3
  have s4a : EuclideanGeometry.angle B M A = EuclideanGeometry.angle C M A := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := A) (Q := B) (Q' := C) (R := M) (R' := M) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_23 A M B] at h; exact h) : LeanBridges.Geometry.Triangle A B M) (by (have h := hH9; rw [LeanBridges.Geometry.triangle_rot_231 M A C] at h; exact h) : LeanBridges.Geometry.Triangle A C M))).mp s3).1.2
  have s4b : EuclideanGeometry.angle M A B = EuclideanGeometry.angle M A C := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := A) (Q := B) (Q' := C) (R := M) (R' := M) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_23 A M B] at h; exact h) : LeanBridges.Geometry.Triangle A B M) (by (have h := hH9; rw [LeanBridges.Geometry.triangle_rot_231 M A C] at h; exact h) : LeanBridges.Geometry.Triangle A C M))).mp s3).2
  -- 5. axi:supplementary-angles A := C, B := M, C := B, D := A, from H5, H8, 1
  have s5 : EuclideanGeometry.angle C M A + EuclideanGeometry.angle A M B = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := C) (B := M) (C := B) (D := A) (by (have h := s1a; rw [sbtw_comm (x := B) (y := M) (z := C)] at h; exact h) : Sbtw ℝ C M B) hH8.1 hH5.2.2.1 hH5.1)
  -- 6. mun:angle-turned P := A, Q := M, R := B, from H8
  have s6 : EuclideanGeometry.angle A M B = EuclideanGeometry.angle B M A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := A) (Q := M) (R := B) hH8.1 (Ne.symm hH8.2.1) hH8.2.2.1)
  -- 7. algebra, from 4, 5, 6
  have s7 : EuclideanGeometry.angle A M B = (90 : ℝ) * Real.pi / 180 := by linear_combination ((90) / ((180))) * s4a + ((16200) / ((180) * (180))) * s5 + ((90) / ((180))) * s6
  -- 8. calculation
  have s8 : EuclideanGeometry.angle B A M = EuclideanGeometry.angle M A C := by
    calc EuclideanGeometry.angle B A M = EuclideanGeometry.angle M A B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := B) (Q := A) (R := M) (Ne.symm hH8.2.2.1) (Ne.symm hH8.1) (Ne.symm hH8.2.1))
      _ = EuclideanGeometry.angle M A C := s4b
  -- 9. join 7, 8
  have s9a : EuclideanGeometry.angle A M B = (90 : ℝ) * Real.pi / 180 := s7
  have s9b : EuclideanGeometry.angle B A M = EuclideanGeometry.angle M A C := s8
  exact ⟨s9a, s9b⟩

end Parley.Proofs.Euclid.IsoscelesMedian.IsoscelesMedian
