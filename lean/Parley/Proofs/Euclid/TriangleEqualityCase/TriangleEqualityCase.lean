module

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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.TriangleEqualityBetween

/-! Written from proofs/euclid/triangle-equality-case.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.TriangleEqualityCase.TriangleEqualityCase

theorem triangle_equality_case (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : dist A C + dist C B = dist A B) (hH5 : C ≠ A) (hH6 : C ≠ B) :
    Sbtw ℝ A C B := by
  -- 1. thm:triangle-equality-between, from H4, H5, H6
  exact (Parley.Stdlib.Geometry.TriangleEqualityBetween.triangle_equality_between (P := A) (Q := C) (R := B) (Ne.symm hH5) hH6 hH4)

end Parley.Proofs.Euclid.TriangleEqualityCase.TriangleEqualityCase
