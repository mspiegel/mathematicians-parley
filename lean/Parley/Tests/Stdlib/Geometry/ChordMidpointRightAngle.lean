module

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

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.ChordMidpointRightAngle

theorem chord_midpoint_right_angle (A : ℂ) (B : ℂ) (M : ℂ) (O : ℂ) (hH5 : Sbtw ℝ A M B ∧ dist A M = dist M B) (hH6 : dist A O = dist B O) (hH7 : O ≠ M) (hH8 : M ≠ B) (hH9 : O ≠ B) :
    EuclideanGeometry.angle O M B = (90 : ℝ) * Real.pi / 180 := by
  -- 1. thm:geometry-chord-midpoint-right-angle, from H5, H6, H7, H8, H9
  exact (Parley.Stdlib.Geometry.ChordMidpointRightAngle.chord_midpoint_right_angle (A := A) (B := B) (M := M) (O := O) hH5 hH6 hH7 hH8 hH9)

end Parley.Tests.Stdlib.Geometry.ChordMidpointRightAngle
