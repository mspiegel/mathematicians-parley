module

public import Geometry
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
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.ChordMidpointRightAngle

/-! Written from proofs/euclid/chord-bisector.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ChordBisector.ChordBisector

theorem chord_bisector (O : ℂ) (A : ℂ) (B : ℂ) (M : ℂ) (hH5 : dist O A = dist O B) (hH6 : Sbtw ℝ A M B ∧ dist A M = dist M B) (hH7 : O ≠ M) (hH8 : M ≠ A) (hH9 : O ≠ A) :
    EuclideanGeometry.angle O M A = (90 : ℝ) * Real.pi / 180 := by
  -- 1. thm:chord-midpoint-right-angle A := B, B := A, from H5, H6, H7, H8, H9
  exact (Parley.Stdlib.Geometry.ChordMidpointRightAngle.chord_midpoint_right_angle (A := B) (B := A) (M := M) (O := O) (by (have h := hH6; rw [LeanBridges.Geometry.midpoint_comm M A B] at h; exact h) : Sbtw ℝ B M A ∧ dist B M = dist M A) (by (have h := hH5.symm; rw [dist_comm O B, dist_comm O A] at h; exact h) : dist B O = dist A O) hH7 hH8 hH9)

end Parley.Proofs.Euclid.ChordBisector.ChordBisector
