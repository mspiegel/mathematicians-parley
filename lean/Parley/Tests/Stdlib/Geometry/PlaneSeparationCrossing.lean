module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.PlaneSeparationCrossing

theorem plane_separation_crossing (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (hH5 : A ≠ B) (hH6 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line A B ∧ Sbtw ℝ P X Q) := by
  -- 1. axi:geometry-plane-separation-crossing, from H5, H6
  exact (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := A) (B := B) (P := P) (Q := Q) hH5 hH6)

end Parley.Tests.Stdlib.Geometry.PlaneSeparationCrossing
