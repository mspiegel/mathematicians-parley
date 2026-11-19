module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from proofs/euclid/midpoint-is-equidistant.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.MidpointIsEquidistant.MidpointIsEquidistant

theorem midpoint_is_equidistant (M : ℂ) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH6 : M = Complex.mk ((a + c) / 2) ((b + d) / 2)) :
    dist (Complex.mk a b) M = dist M (Complex.mk c d) := by
  -- 1. mun:distance-by-coordinates
  have s1 : dist (Complex.mk a b) (Complex.mk ((a + c) / 2) ((b + d) / 2)) = Real.sqrt ((a - (a + c) / 2) ^ 2 + (b - (b + d) / 2) ^ 2) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_by_coordinates (a := a) (b := b) (c := (a + c) / 2) (d := (b + d) / 2))
  -- 2. substitute M = ((a + c)/2, (b + d)/2) (H6) into line 1
  have s2 : dist (Complex.mk a b) M = Real.sqrt ((a - (a + c) / 2) ^ 2 + (b - (b + d) / 2) ^ 2) := Eq.subst (motive := (fun t : ℂ => dist (Complex.mk a b) t = Real.sqrt ((a - (a + c) / 2) ^ 2 + (b - (b + d) / 2) ^ 2))) hH6.symm s1
  -- 3. mun:distance-by-coordinates
  have s3 : dist (Complex.mk ((a + c) / 2) ((b + d) / 2)) (Complex.mk c d) = Real.sqrt (((a + c) / 2 - c) ^ 2 + ((b + d) / 2 - d) ^ 2) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_by_coordinates (a := (a + c) / 2) (b := (b + d) / 2) (c := c) (d := d))
  -- 4. substitute M = ((a + c)/2, (b + d)/2) (H6) into line 3
  have s4 : dist M (Complex.mk c d) = Real.sqrt (((a + c) / 2 - c) ^ 2 + ((b + d) / 2 - d) ^ 2) := Eq.subst (motive := (fun t : ℂ => dist t (Complex.mk c d) = Real.sqrt (((a + c) / 2 - c) ^ 2 + ((b + d) / 2 - d) ^ 2))) hH6.symm s3
  -- 5. substitute
  have s5 : dist (Complex.mk a b) M = Real.sqrt (((a + c) / 2 - c) ^ 2 + ((b + d) / 2 - d) ^ 2) := by
    have c1 : (a - (a + c) / 2) ^ 2 + (b - (b + d) / 2) ^ 2 = ((a + c) / 2 - c) ^ 2 + ((b + d) / 2 - d) ^ 2 := by ring1
    have row1 : dist (Complex.mk a b) M = Real.sqrt (((a + c) / 2 - c) ^ 2 + ((b + d) / 2 - d) ^ 2) := Eq.subst (motive := (fun t : ℝ => dist (Complex.mk a b) M = Real.sqrt t)) c1 s2
    exact row1
  -- 6. calculation
  calc dist (Complex.mk a b) M = Real.sqrt (((a + c) / 2 - c) ^ 2 + ((b + d) / 2 - d) ^ 2) := s5
    _ = dist M (Complex.mk c d) := s4.symm

end Parley.Proofs.Euclid.MidpointIsEquidistant.MidpointIsEquidistant
