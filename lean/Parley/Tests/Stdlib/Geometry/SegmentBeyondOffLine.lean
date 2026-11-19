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

namespace Parley.Tests.Stdlib.Geometry.SegmentBeyondOffLine

theorem segment_beyond_off_line (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (X : ℂ) (hH6 : A ≠ B) (hH7 : Q ∈ LeanBridges.Geometry.line A B) (hH8 : ¬ X ∈ LeanBridges.Geometry.line A B) (hH9 : Sbtw ℝ P X Q) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((X - A) / (B - A)) := by
  -- 1. mun:geometry-segment-beyond-off-line, from H6, H7, H8, H9
  exact (Parley.Items.Stdlib.Geometry.mun_segment_beyond_off_line (A := A) (B := B) (P := P) (Q := Q) (X := X) hH6 hH7 hH8 hH9)

end Parley.Tests.Stdlib.Geometry.SegmentBeyondOffLine
