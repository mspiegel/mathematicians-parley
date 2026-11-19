module

public import Geometry
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Wiedijk.AngleSum.AngleSum

/-! Written from proofs/euclid/two-angles-under-straight.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.TwoAnglesUnderStraight.TwoAnglesUnderStraight

theorem two_angles_under_straight (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) :
    EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C < (180 : ℝ) * Real.pi / 180 := by
  -- 1. mun:angle-real P := B, Q := C, R := A, from H4
  have s1 : EuclideanGeometry.angle B C A ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_angle_real_2 (P := B) (Q := C) (R := A) hH4.2.1 hH4.2.2.1 (Ne.symm hH4.1))
  -- 2. mun:sine-positive P := B, Q := C, R := A, from H4
  have s2 : Real.sin (EuclideanGeometry.angle B C A) > 0 := by exact (Parley.Items.Stdlib.Geometry.mun_sine_positive (P := B) (Q := C) (R := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A))
  -- 3. contradiction
  have s3 : EuclideanGeometry.angle B C A > 0 := by
    by_contra hS
    -- 3.1. inequalities, from S
    have s3_1 : EuclideanGeometry.angle B C A ≤ 0 := by linarith only [hS]
    -- 3.2. antisymmetry, from 1, 3.1
    have s3_2 : EuclideanGeometry.angle B C A = 0 := le_antisymm s3_1 s1
    -- 3.3. substitute ∠BCA = 0 (line 3.2) into line 2
    have s3_3 : Real.sin (0 : ℝ) > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => Real.sin t > 0)) s3_2 s2; revert h; norm_num)
    have hn : ¬ (Real.sin (0 : ℝ) > 0) := by
      have hv1 : Real.sin (0 : ℝ) = 0 := by rw [Real.sin_zero]
      have hf1 : 0 - Real.sin (0 : ℝ) = 0 := by linear_combination (-1) * hv1
      exact not_lt.mpr (by linarith only [hf1])
    exact absurd s3_3 hn
  -- 4. inequalities
  have s4 : EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C < EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A := by linarith only [s3]
  -- 5. calculation
  calc EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C < EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A := s4
    _ = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Proofs.Wiedijk.AngleSum.AngleSum.angle_sum (A := A) (B := B) (C := C) hH4)

end Parley.Proofs.Euclid.TwoAnglesUnderStraight.TwoAnglesUnderStraight
