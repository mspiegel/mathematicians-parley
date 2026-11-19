module

public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.MidpointHalves

theorem midpoint_halves (M : ℂ) (A : ℂ) (B : ℂ) (hH4 : Sbtw ℝ A M B ∧ dist A M = dist M B) :
    dist A M = dist A B / 2 := by
  -- 1. def:geometry-midpoint, from H4
  have s1a : Sbtw ℝ A M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH4).1
  have s1b : dist A M = dist M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH4).2
  -- 2. mun:geometry-segment-addition, from 1
  have s2 : dist A M + dist M B = dist A B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := B) (S := M) s1a)
  -- 3. algebra, from 1, 2
  linear_combination ((1) / (((2 : ℝ)))) * s1b + ((1) / (((2 : ℝ)))) * s2

end Parley.Tests.Stdlib.Geometry.MidpointHalves
