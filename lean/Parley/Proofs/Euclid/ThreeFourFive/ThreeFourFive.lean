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
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras

/-! Written from proofs/euclid/three-four-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ThreeFourFive.ThreeFourFive

theorem three_four_five (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : dist B C = 3) (hH6 : dist C A = 4) (hH7 : dist A B = 5) :
    EuclideanGeometry.angle B C A = (90 : ℝ) * Real.pi / 180 := by
  -- 1. substitute |AB| = 5 (H7)
  have s1 : dist A B ^ 2 = 5 ^ 2 := congrArg (fun t : ℝ => t ^ 2) hH7
  -- 2. substitute |AC| = 4 (H6)
  have s2 : dist A C ^ 2 = 4 ^ 2 := congrArg (fun t : ℝ => t ^ 2) (by (have h := hH6; rw [dist_comm C A] at h; exact h) : dist A C = 4)
  -- 3. substitute |BC| = 3 (H5)
  have s3 : dist B C ^ 2 = 3 ^ 2 := congrArg (fun t : ℝ => t ^ 2) hH5
  -- 4. algebra, from 1, 2, 3
  have s4 : dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 := by linear_combination s1 + (-1) * s2 + (-1) * s3
  -- 5. calculation
  calc EuclideanGeometry.angle B C A = EuclideanGeometry.angle A C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := C) (R := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B)).symm
    _ = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Proofs.Euclid.ConverseOfPythagoras.ConverseOfPythagoras.converse_of_pythagoras (A := A) (B := B) (C := C) hH4 s4)

end Parley.Proofs.Euclid.ThreeFourFive.ThreeFourFive
