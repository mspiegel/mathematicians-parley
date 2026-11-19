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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.AngleAngleSimilar

/-! Written from proofs/wiedijk/pythagoras.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Pythagoras.SimilarTriangles

theorem similar_triangles (P : ℂ) (Q : ℂ) (R : ℂ) (P' : ℂ) (Q' : ℂ) (R' : ℂ) (hH7 : LeanBridges.Geometry.Triangle P Q R) (hH8 : LeanBridges.Geometry.Triangle P' Q' R') (hH9 : EuclideanGeometry.angle Q P R = EuclideanGeometry.angle Q' P' R') (hH10 : EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R') :
    dist P Q * dist P' R' = dist P' Q' * dist P R := by
  -- 1. thm:angle-angle-similar, from H7, H8, H9, H10
  exact (Parley.Stdlib.Geometry.AngleAngleSimilar.angle_angle_similar (P := P) (Q := Q) (R := R) (P' := P') (Q' := Q') (R' := R') hH7 hH8 hH9 hH10)

end Parley.Proofs.Wiedijk.Pythagoras.SimilarTriangles
