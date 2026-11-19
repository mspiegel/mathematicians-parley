module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.GreaterSideGreaterAngle

/-! Written from proofs/euclid/greater-side-greater-angle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.GreaterSideGreaterAngle.GreaterSideGreaterAngle

theorem greater_side_greater_angle (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : dist C A > dist C B) :
    EuclideanGeometry.angle C B A > EuclideanGeometry.angle C A B := by
  -- 1. thm:euclid-18 A := C, C := A, from H4, H5
  exact (Parley.Stdlib.Geometry.GreaterSideGreaterAngle.greater_side_greater_angle (A := C) (B := B) (C := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C B A) hH5)

end Parley.Proofs.Euclid.GreaterSideGreaterAngle.GreaterSideGreaterAngle
