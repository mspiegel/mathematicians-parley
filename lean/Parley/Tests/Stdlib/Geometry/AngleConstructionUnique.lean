module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Data.Set.Defs
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.AngleConstructionUnique

theorem angle_construction_unique (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (hH6 : LeanBridges.Geometry.Triangle A B C) (hH7 : 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A))) (hH8 : 0 < Complex.im ((E - A) / (B - A)) * Complex.im ((C - A) / (B - A))) (hH9 : EuclideanGeometry.angle B A D = EuclideanGeometry.angle B A E) :
    E ∈ LeanBridges.Geometry.ray A D := by
  -- 1. axi:geometry-angle-construction-unique, from H6, H7, H8, H9
  exact (Parley.Items.Stdlib.Geometry.axi_angle_construction_unique (E := E) (A := A) (B := B) (C := C) (D := D) hH6 hH7 hH8 hH9)

end Parley.Tests.Stdlib.Geometry.AngleConstructionUnique
