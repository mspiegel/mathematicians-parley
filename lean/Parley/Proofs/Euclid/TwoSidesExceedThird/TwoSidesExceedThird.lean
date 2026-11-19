module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.TriangleInequalityStrict

/-! Written from proofs/euclid/two-sides-exceed-third.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.TwoSidesExceedThird.TwoSidesExceedThird

theorem two_sides_exceed_third (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) :
    dist A C < dist A B + dist B C := by
  -- 1. thm:triangle-inequality-strict P := A, Q := B, R := C, from H4
  exact (Parley.Stdlib.Geometry.TriangleInequalityStrict.triangle_inequality_strict (P := A) (Q := B) (R := C) hH4)

end Parley.Proofs.Euclid.TwoSidesExceedThird.TwoSidesExceedThird
