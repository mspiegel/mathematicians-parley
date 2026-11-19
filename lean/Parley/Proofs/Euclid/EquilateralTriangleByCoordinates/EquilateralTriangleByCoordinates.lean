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
public import Mathlib.Analysis.Real.Sqrt
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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Euclid.EquilateralAngleSixty.EquilateralAngleSixty

/-! Written from proofs/euclid/equilateral-triangle-by-coordinates.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.EquilateralTriangleByCoordinates.EquilateralTriangleByCoordinates

theorem equilateral_triangle_by_coordinates (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : A = Complex.mk (0 : ℝ) (0 : ℝ)) (hH5 : B = Complex.mk (2 : ℝ) (0 : ℝ)) (hH6 : C = Complex.mk (1 : ℝ) (Real.sqrt (3 : ℝ))) (hH7 : LeanBridges.Geometry.Triangle B A C) :
    dist A B = 2 ∧ dist B C = 2 ∧ dist C A = 2 ∧ EuclideanGeometry.angle B A C = (60 : ℝ) * Real.pi / 180 := by
  -- 1. calculation
  have s1 : dist A B = 2 := by
    calc dist A B = Real.sqrt ((0 - 2) ^ 2 + (0 - 0) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := A) (B := B) (a := (0 : ℝ)) (b := (0 : ℝ)) (c := (2 : ℝ)) (d := (0 : ℝ)) hH4 hH5)
      _ = Real.sqrt (4 : ℝ) := by norm_num
      _ = 2 := by
          have hv1 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          linear_combination hv1
  -- 2. calculation
  have s2 : dist B C = 2 := by
    calc dist B C = Real.sqrt ((2 - 1) ^ 2 + (0 - Real.sqrt (3 : ℝ)) ^ 2) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := B) (B := C) (a := (2 : ℝ)) (b := (0 : ℝ)) (c := (1 : ℝ)) (d := Real.sqrt (3 : ℝ)) hH5 hH6)
      _ = Real.sqrt (4 : ℝ) := by
          have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
          have hv1 : Real.sqrt ((2 - 1) ^ 2 + (0 - Real.sqrt (3 : ℝ)) ^ 2) = 2 := by rw [congrArg Real.sqrt (show ((2 - 1) ^ 2 + (0 - Real.sqrt (3 : ℝ)) ^ 2 : ℝ) = 2 ^ 2 by linear_combination hr3), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          have hv2 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          linear_combination hv1 + (-1) * hv2
      _ = 2 := by
          have hv1 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          linear_combination hv1
  -- 3. calculation
  have s3 : dist C A = 2 := by
    calc dist C A = Real.sqrt ((1 - 0) ^ 2 + (Real.sqrt (3 : ℝ) - 0) ^ 2) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := C) (B := A) (a := (1 : ℝ)) (b := Real.sqrt (3 : ℝ)) (c := (0 : ℝ)) (d := (0 : ℝ)) hH6 hH4)
      _ = Real.sqrt (4 : ℝ) := by
          have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
          have hv1 : Real.sqrt ((1 - 0) ^ 2 + (Real.sqrt (3 : ℝ) - 0) ^ 2) = 2 := by rw [congrArg Real.sqrt (show ((1 - 0) ^ 2 + (Real.sqrt (3 : ℝ) - 0) ^ 2 : ℝ) = 2 ^ 2 by linear_combination hr3), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          have hv2 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          linear_combination hv1 + (-1) * hv2
      _ = 2 := by
          have hv1 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          linear_combination hv1
  -- 4. calculation
  have s4 : dist B A = dist A C := by
    calc dist B A = 2 := (by (have h := s1; rw [dist_comm A B] at h; exact h) : dist B A = 2)
      _ = dist A C := (by (have h := s3.symm; rw [dist_comm C A] at h; exact h) : 2 = dist A C)
  -- 5. calculation
  have s5 : dist A C = dist C B := by
    calc dist A C = 2 := (by (have h := s3; rw [dist_comm C A] at h; exact h) : dist A C = 2)
      _ = dist C B := (by (have h := s2.symm; rw [dist_comm B C] at h; exact h) : 2 = dist C B)
  -- 6. thm:equilateral-angle-sixty A := B, B := A, from H7, 4, 5
  have s6 : EuclideanGeometry.angle B A C = (60 : ℝ) * Real.pi / 180 := by exact (Parley.Proofs.Euclid.EquilateralAngleSixty.EquilateralAngleSixty.equilateral_angle_sixty (A := B) (B := A) (C := C) hH7 ⟨s4, s5⟩)
  -- 7. join 1, 2, 3, 6
  have s7a : dist A B = 2 := s1
  have s7b : dist B C = 2 := s2
  have s7c : dist C A = 2 := s3
  have s7d : EuclideanGeometry.angle B A C = (60 : ℝ) * Real.pi / 180 := s6
  exact ⟨s7a, s7b, s7c, s7d⟩

end Parley.Proofs.Euclid.EquilateralTriangleByCoordinates.EquilateralTriangleByCoordinates
