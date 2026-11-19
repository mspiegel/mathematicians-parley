module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
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
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Stdlib.Geometry.Pythagoras
public import Parley.Stdlib.Geometry.RayPoint
public import Parley.Stdlib.Geometry.SideSideSide

/-! Written from proofs/euclid/converse-of-pythagoras.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras

theorem converse_of_pythagoras (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2) :
    EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180 := by
  -- 1. obtain E: axi:angle-construction A := C, C := A, x := 90°, from H4
  have r29_1 : (90 : ℝ) * Real.pi / 180 > (0 : ℝ) * Real.pi / 180 := by
    have hf1 : 3 < Real.pi := Real.pi_gt_three
    have hf2 : Real.pi < 4 := Real.pi_lt_four
    linarith only [hf1, hf2]
  have r29_2 : (90 : ℝ) * Real.pi / 180 < (180 : ℝ) * Real.pi / 180 := by
    have hf1 : 3 < Real.pi := Real.pi_gt_three
    have hf2 : Real.pi < 4 := Real.pi_lt_four
    linarith only [hf1, hf2]
  obtain ⟨E, s1a, ⟨s1b, s1c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_angle_construction (A := C) (B := B) (C := A) (x := (90 : ℝ) * Real.pi / 180) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C B A) r29_1 r29_2)
  -- 2. mun:same-side-off-line A := C, P := E, Q := A, from 1
  have s2 : ¬ E ∈ LeanBridges.Geometry.line C B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := C) (B := B) (P := E) (Q := A) s1b)
  -- 3. mun:triangle-off-line P := E, Q := C, R := B, from H4, 2
  have s3 : LeanBridges.Geometry.Triangle E C B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := E) (Q := C) (R := B) (Ne.symm hH4.2.1) s2)
  -- 4. axi:distance-positive P := C, Q := A, from H4
  have s4 : dist C A > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := C) (Q := A) (Ne.symm hH4.2.2.1))
  -- 5. obtain D: mun:ray-point A := C, B := E, C := B, r := |CA|, from 3, 4
  obtain ⟨D, s5a, ⟨⟨s5b, s5c⟩, s5d⟩⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := C) (B := E) (C := B) (r := dist C A) (by (have h := s3; rw [LeanBridges.Geometry.triangle_swap_12 E C B] at h; exact h) : LeanBridges.Geometry.Triangle C E B) s4)
  -- 6. mun:same-side-off-line A := C, P := D, Q := E, from 5
  have s6 : ¬ D ∈ LeanBridges.Geometry.line C B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := C) (B := B) (P := D) (Q := E) s5c)
  -- 7. mun:triangle-off-line P := D, Q := C, R := B, from H4, 6
  have s7 : LeanBridges.Geometry.Triangle D C B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := C) (R := B) (Ne.symm hH4.2.1) s6)
  -- 8. calculation
  have s8 : EuclideanGeometry.angle D C B = (90 : ℝ) * Real.pi / 180 := by
    calc EuclideanGeometry.angle D C B = EuclideanGeometry.angle B C D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := D) (Q := C) (R := B) s7.1 (Ne.symm s7.2.1) s7.2.2.1)
      _ = EuclideanGeometry.angle B C E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := C) (Q := E) (R := B) (X := D) s5b s5c)
      _ = (90 : ℝ) * Real.pi / 180 := s1c
  -- 9. thm:pythagoras A := D, from 7, 8
  have s9 : dist D B ^ 2 = dist D C ^ 2 + dist B C ^ 2 := by exact (Parley.Stdlib.Geometry.Pythagoras.pythagoras (A := D) (B := B) (C := C) (by (have h := s7; rw [LeanBridges.Geometry.triangle_swap_23 D C B] at h; exact h) : LeanBridges.Geometry.Triangle D B C) s8)
  -- 10. algebra, from H5, 5, 9
  have s10 : dist D B ^ 2 = dist A B ^ 2 := by
    rw [dist_comm C A] at s5d
    rw [dist_comm D B, dist_comm D C] at s9
    rw [dist_comm D B]
    exact (by linear_combination (-1) * hH5 + (dist A C + dist C D) * s5d + s9)
  -- 11. mun:square-equal x := |DB|, y := |AB|, from 10
  have r65_1 : dist D B ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := D) (Q := B))
  have r65_2 : dist A B ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := A) (Q := B))
  have s11 : dist D B = dist A B := by exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := dist D B) (y := dist A B) r65_1 r65_2)).mp s10
  -- 12. thm:side-side-side B := C, C := B, E := C, F := B, from H4, 5, 7, 11
  have s12 : dist A C = dist D C ∧ dist C B = dist C B ∧ dist B A = dist B D ∧ EuclideanGeometry.angle A C B = EuclideanGeometry.angle D C B ∧ EuclideanGeometry.angle C B A = EuclideanGeometry.angle C B D ∧ EuclideanGeometry.angle B A C = EuclideanGeometry.angle B D C := by exact (Parley.Stdlib.Geometry.SideSideSide.side_side_side (A := A) (B := C) (C := B) (D := D) (E := C) (F := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s7 (by (have h := s5d.symm; rw [dist_comm C A, dist_comm C D] at h; exact h) : dist A C = dist D C) rfl (by (have h := s11.symm; rw [dist_comm A B, dist_comm D B] at h; exact h) : dist B A = dist B D))
  -- 13. def:congruent P := A, Q := C, R := B, P′ := D, Q′ := C, R′ := B, from H4, 7, 12
  have s13 : EuclideanGeometry.angle A C B = EuclideanGeometry.angle D C B := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := D) (Q := C) (Q' := C) (R := B) (R' := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s7)).mp s12).1.1.2
  -- 14. transitivity, from 13, 8
  exact Eq.trans s13 s8

end Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras
