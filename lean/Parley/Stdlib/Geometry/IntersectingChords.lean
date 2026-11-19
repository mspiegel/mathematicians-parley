module

public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.PowerOfAPoint

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.IntersectingChords

theorem intersecting_chords (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (O : ℂ) (hH7 : Sbtw ℝ A P B) (hH8 : Sbtw ℝ C P D) (hH9 : dist A O = dist B O) (hH10 : dist A O = dist C O) (hH11 : dist A O = dist D O) :
    dist P A * dist P B = dist P C * dist P D := by
  -- 1. thm:power-of-a-point, from H7, H9
  have s1 : dist A O ^ 2 - dist P O ^ 2 = dist P A * dist P B := by exact (Parley.Stdlib.Geometry.PowerOfAPoint.power_of_a_point (A := A) (B := B) (P := P) (O := O) hH7 hH9)
  -- 2. transitivity, from H10, H11
  have s2 : dist C O = dist D O := by exact Eq.trans hH10.symm hH11
  -- 3. thm:power-of-a-point A := C, B := D, from H8, 2
  have s3 : dist C O ^ 2 - dist P O ^ 2 = dist P C * dist P D := by exact (Parley.Stdlib.Geometry.PowerOfAPoint.power_of_a_point (A := C) (B := D) (P := P) (O := O) hH8 s2)
  -- 4. algebra, from H10, 1, 3
  linear_combination (dist A O + dist C O) * hH10 + (-1) * s1 + s3

end Parley.Stdlib.Geometry.IntersectingChords
