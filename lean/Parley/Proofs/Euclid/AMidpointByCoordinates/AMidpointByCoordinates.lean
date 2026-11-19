module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from proofs/euclid/a-midpoint-by-coordinates.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.AMidpointByCoordinates.AMidpointByCoordinates

theorem a_midpoint_by_coordinates (A : ℂ) (B : ℂ) (M : ℂ) (hH4 : A = Complex.mk (-1 : ℝ) (1 : ℝ)) (hH5 : B = Complex.mk (7 : ℝ) (-4 : ℝ)) (hH6 : M = Complex.mk (3 : ℝ) (-(3 / 2) : ℝ)) :
    dist A M = dist M B ∧ Sbtw ℝ A M B := by
  -- 1. calculation
  have s1 : dist A M = dist M B := by
    calc dist A M = Real.sqrt ((-1 - 3) ^ 2 + (1 - -(3 / 2)) ^ 2 : ℝ) := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := A) (B := M) (a := (-1 : ℝ)) (b := (1 : ℝ)) (c := (3 : ℝ)) (d := (-(3 / 2) : ℝ)) hH4 hH6)
      _ = Real.sqrt (89 / 4 : ℝ) := by norm_num
      _ = Real.sqrt ((3 - 7) ^ 2 + (-(3 / 2) - -4) ^ 2 : ℝ) := by norm_num
      _ = dist M B := by exact (Parley.Items.Stdlib.Geometry.mun_distance_of_points_by_coordinates (A := M) (B := B) (a := (3 : ℝ)) (b := (-(3 / 2) : ℝ)) (c := (7 : ℝ)) (d := (-4 : ℝ)) hH6 hH5).symm
  -- 2. arithmetic
  have s2 : ((-1 - 3) * (-4 - -(3 / 2)) : ℚ) = (7 - 3) * (1 - -(3 / 2)) := by norm_num
  -- 3. arithmetic
  have s3 : ((-1 - 3) * (7 - 3) + (1 - -(3 / 2)) * (-4 - -(3 / 2)) : ℚ) < 0 := by norm_num
  -- 4. mun:between-by-coordinates, from 2, 3
  have s4 : Sbtw ℝ (Complex.mk (-1 : ℝ) (1 : ℝ)) (Complex.mk (3 : ℝ) (-(3 / 2) : ℝ)) (Complex.mk (7 : ℝ) (-4 : ℝ)) := ((Parley.Items.Stdlib.Geometry.mun_between_by_coordinates (a := (-1 : ℝ)) (b := (1 : ℝ)) (c := (3 : ℝ)) (d := (-(3 / 2) : ℝ)) (e := (7 : ℝ)) (f := (-4 : ℝ)))).mpr ⟨by norm_num, by norm_num⟩
  -- 5. substitute
  have s5 : Sbtw ℝ A M B := by
    have c1 : Complex.mk (-1 : ℝ) (1 : ℝ) = A := congrArg (fun t : ℂ => t) hH4.symm
    have row1 : Sbtw ℝ A (Complex.mk (3 : ℝ) (-(3 / 2) : ℝ)) (Complex.mk (7 : ℝ) (-4 : ℝ)) := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ t (Complex.mk (3 : ℝ) (-(3 / 2) : ℝ)) (Complex.mk (7 : ℝ) (-4 : ℝ)))) c1 s4
    have c2 : Complex.mk (3 : ℝ) (-(3 / 2) : ℝ) = M := congrArg (fun t : ℂ => t) hH6.symm
    have row2 : Sbtw ℝ A M (Complex.mk (7 : ℝ) (-4 : ℝ)) := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ A t (Complex.mk (7 : ℝ) (-4 : ℝ)))) c2 row1
    have c3 : Complex.mk (7 : ℝ) (-4 : ℝ) = B := congrArg (fun t : ℂ => t) hH5.symm
    have row3 : Sbtw ℝ A M B := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ A M t)) c3 row2
    exact row3
  -- 6. join 1, 5
  have s6a : dist A M = dist M B := s1
  have s6b : Sbtw ℝ A M B := s5
  exact ⟨s6a, s6b⟩

end Parley.Proofs.Euclid.AMidpointByCoordinates.AMidpointByCoordinates
