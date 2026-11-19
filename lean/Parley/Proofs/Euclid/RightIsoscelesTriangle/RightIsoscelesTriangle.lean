module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
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

/-! Written from proofs/euclid/right-isosceles-triangle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.RightIsoscelesTriangle.RightIsoscelesTriangle

theorem right_isosceles_triangle (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : A = Complex.mk (-2 : ℝ) (-1 : ℝ)) (hH5 : B = Complex.mk (2 : ℝ) (2 : ℝ)) (hH6 : C = Complex.mk (5 : ℝ) (-2 : ℝ)) :
    dist A B = 5 ∧ dist B C = 5 ∧ dist A C ^ 2 = dist A B ^ 2 + dist B C ^ 2 := by
  -- 1. calculation
  have s1 : dist A B = 5 := by
    calc dist A B = Real.sqrt ((-2 - 2) ^ 2 + (-1 - 2) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := A) (B := B) (a := (-2 : ℝ)) (b := (-1 : ℝ)) (c := (2 : ℝ)) (d := (2 : ℝ)) hH4 hH5)
      _ = Real.sqrt (25 : ℝ) := by norm_num
      _ = 5 := by
          have hv1 : Real.sqrt (25 : ℝ) = 5 := by rw [congrArg Real.sqrt (show (25 : ℝ) = 5 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
          linear_combination hv1
  -- 2. calculation
  have s2 : dist B C = 5 := by
    calc dist B C = Real.sqrt ((2 - 5) ^ 2 + (2 - -2) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := B) (B := C) (a := (2 : ℝ)) (b := (2 : ℝ)) (c := (5 : ℝ)) (d := (-2 : ℝ)) hH5 hH6)
      _ = Real.sqrt (25 : ℝ) := by norm_num
      _ = 5 := by
          have hv1 : Real.sqrt (25 : ℝ) = 5 := by rw [congrArg Real.sqrt (show (25 : ℝ) = 5 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
          linear_combination hv1
  -- 3. mun:distance-of-points-by-coordinates, from H4, H6
  have s3 : dist A C = Real.sqrt ((-2 - 5) ^ 2 + (-1 - -2) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := A) (B := C) (a := (-2 : ℝ)) (b := (-1 : ℝ)) (c := (5 : ℝ)) (d := (-2 : ℝ)) hH4 hH6)
  -- 4. substitute |AB| = 5 (line 1)
  have s4 : dist A B ^ 2 + dist B C ^ 2 = 5 ^ 2 + dist B C ^ 2 := congrArg (fun t : ℝ => t ^ 2 + dist B C ^ 2) s1
  -- 5. substitute |BC| = 5 (line 2) into line 4
  have s5 : dist A B ^ 2 + dist B C ^ 2 = 5 ^ 2 + 5 ^ 2 := Eq.subst (motive := (fun t : ℝ => dist A B ^ 2 + dist B C ^ 2 = 5 ^ 2 + t ^ 2)) s2 s4
  -- 6. calculation
  have s6 : dist A C ^ 2 = dist A B ^ 2 + dist B C ^ 2 := by
    calc dist A C ^ 2 = Real.sqrt ((-2 - 5) ^ 2 + (-1 - -2) ^ 2 : ℝ) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s3
      _ = 50 := by
          have hv1 : Real.sqrt ((-2 - 5) ^ 2 + (-1 - -2) ^ 2 : ℝ) = 5 * Real.sqrt (2 : ℝ) := by rw [congrArg Real.sqrt (show ((-2 - 5) ^ 2 + (-1 - -2) ^ 2 : ℝ) = 5 ^ 2 * 2 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 5 ^ 2 by positivity) 2, Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
          have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
          linear_combination (Real.sqrt ((-2 - 5) ^ 2 + (-1 - -2) ^ 2 : ℝ) + 5 * Real.sqrt (2 : ℝ)) * hv1 + (25) * hr2
      _ = 5 ^ 2 + 5 ^ 2 := by norm_num
      _ = dist A B ^ 2 + dist B C ^ 2 := s5.symm
  -- 7. join 1, 2, 6
  have s7a : dist A B = 5 := s1
  have s7b : dist B C = 5 := s2
  have s7c : dist A C ^ 2 = dist A B ^ 2 + dist B C ^ 2 := s6
  exact ⟨s7a, s7b, s7c⟩

end Parley.Proofs.Euclid.RightIsoscelesTriangle.RightIsoscelesTriangle
