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
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras

/-! Written from proofs/euclid/angle-in-a-semicircle-by-coordinates.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.AngleInASemicircleByCoordinates.AngleInASemicircleByCoordinates

theorem angle_in_a_semicircle_by_coordinates (A : ℂ) (B : ℂ) (C : ℂ) (O : ℂ) (hH5 : A = Complex.mk (-5 : ℝ) (0 : ℝ)) (hH6 : B = Complex.mk (5 : ℝ) (0 : ℝ)) (hH7 : C = Complex.mk (3 : ℝ) (4 : ℝ)) (hH8 : O = Complex.mk (0 : ℝ) (0 : ℝ)) (hH9 : LeanBridges.Geometry.Triangle A C B) :
    dist O C = 5 ∧ EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180 := by
  -- 1. calculation
  have s1 : dist O C = 5 := by
    calc dist O C = Real.sqrt ((0 - 3) ^ 2 + (0 - 4) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := O) (B := C) (a := (0 : ℝ)) (b := (0 : ℝ)) (c := (3 : ℝ)) (d := (4 : ℝ)) hH8 hH7)
      _ = Real.sqrt (25 : ℝ) := by norm_num
      _ = 5 := by
          have hv1 : Real.sqrt (25 : ℝ) = 5 := by rw [congrArg Real.sqrt (show (25 : ℝ) = 5 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
          linear_combination hv1
  -- 2. calculation
  have s2 : dist A C = Real.sqrt (80 : ℝ) := by
    calc dist A C = Real.sqrt ((-5 - 3) ^ 2 + (0 - 4) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := A) (B := C) (a := (-5 : ℝ)) (b := (0 : ℝ)) (c := (3 : ℝ)) (d := (4 : ℝ)) hH5 hH7)
      _ = Real.sqrt (80 : ℝ) := by norm_num
  -- 3. calculation
  have s3 : dist C B = Real.sqrt (20 : ℝ) := by
    calc dist C B = Real.sqrt ((3 - 5) ^ 2 + (4 - 0) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := C) (B := B) (a := (3 : ℝ)) (b := (4 : ℝ)) (c := (5 : ℝ)) (d := (0 : ℝ)) hH7 hH6)
      _ = Real.sqrt (20 : ℝ) := by norm_num
  -- 4. calculation
  have s4 : dist B A = 10 := by
    calc dist B A = Real.sqrt ((5 - -5) ^ 2 + (0 - 0) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := B) (B := A) (a := (5 : ℝ)) (b := (0 : ℝ)) (c := (-5 : ℝ)) (d := (0 : ℝ)) hH6 hH5)
      _ = Real.sqrt (100 : ℝ) := by norm_num
      _ = 10 := by
          have hv1 : Real.sqrt (100 : ℝ) = 10 := by rw [congrArg Real.sqrt (show (100 : ℝ) = 10 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 10 by norm_num)]
          linear_combination hv1
  -- 5. calculation
  have s5 : dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 := by
    calc dist A B ^ 2 = 10 ^ 2 := by
          rw [dist_comm A B]
          (have h := congrArg (fun t : ℝ => t ^ 2) s4; push_cast at h ⊢; exact_mod_cast h)
      _ = 80 + 20 := by norm_num
      _ = Real.sqrt (80 : ℝ) ^ 2 + Real.sqrt (20 : ℝ) ^ 2 := by
          have hv1 : Real.sqrt (20 : ℝ) = 2 * Real.sqrt (5 : ℝ) := by rw [congrArg Real.sqrt (show (20 : ℝ) = 2 ^ 2 * 5 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by positivity) 5, Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          have hv2 : Real.sqrt (80 : ℝ) = 4 * Real.sqrt (5 : ℝ) := by rw [congrArg Real.sqrt (show (80 : ℝ) = 4 ^ 2 * 5 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 4 ^ 2 by positivity) 5, Real.sqrt_sq (show (0 : ℝ) ≤ 4 by norm_num)]
          have hr5 : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
          linear_combination (-Real.sqrt (20 : ℝ) - 2 * Real.sqrt (5 : ℝ)) * hv1 + (-(4 * Real.sqrt (5 : ℝ)) - Real.sqrt (80 : ℝ)) * hv2 + (-20) * hr5
      _ = dist A C ^ 2 + Real.sqrt (20 : ℝ) ^ 2 := congrArg (fun t : ℝ => t ^ 2 + Real.sqrt (20 : ℝ) ^ 2) s2.symm
      _ = dist A C ^ 2 + dist B C ^ 2 := by (have h := (by (have h := congrArg (fun t : ℝ => dist A C ^ 2 + t ^ 2) s3.symm; rw [dist_comm C B] at h; exact h) : dist A C ^ 2 + Real.sqrt (20 : ℝ) ^ 2 = dist A C ^ 2 + dist B C ^ 2); push_cast at h ⊢; exact_mod_cast h)
  -- 6. thm:converse-of-pythagoras, from H9, 5
  have s6 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras.converse_of_pythagoras (A := A) (B := B) (C := C) (by (have h := hH9; rw [LeanBridges.Geometry.triangle_swap_23 A C B] at h; exact h) : LeanBridges.Geometry.Triangle A B C) s5)
  -- 7. join 1, 6
  have s7a : dist O C = 5 := s1
  have s7b : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180 := s6
  exact ⟨s7a, s7b⟩

end Parley.Proofs.Euclid.AngleInASemicircleByCoordinates.AngleInASemicircleByCoordinates
