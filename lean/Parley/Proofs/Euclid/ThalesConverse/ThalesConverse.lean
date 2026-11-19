module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Euclid.Apollonius.Apollonius
public import Parley.Proofs.Wiedijk.Pythagoras.Pythagoras

/-! Written from proofs/euclid/thales-converse.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ThalesConverse.ThalesConverse

theorem thales_converse (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180) (hH7 : Sbtw ℝ A M B ∧ dist A M = dist M B) :
    dist M C = dist M A := by
  -- 1. def:midpoint, from H7
  have s1a : Sbtw ℝ A M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH7).1
  have s1b : dist A M = dist M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH7).2
  -- 2. thm:apollonius A := C, B := A, C := B, from 1
  have s2 : dist C A ^ 2 + dist C B ^ 2 = 2 * dist C M ^ 2 + 2 * dist A M ^ 2 := by exact (Parley.Proofs.Euclid.Apollonius.Apollonius.apollonius (A := C) (B := A) (C := B) (M := M) s1a s1b)
  -- 3. mun:segment-addition P := A, Q := B, S := M, from 1
  have s3 : dist A M + dist M B = dist A B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := B) (S := M) s1a)
  -- 4. algebra, from 1, 3
  have s4 : dist A B = 2 * dist A M := by linear_combination (-1) * s1b + (-1) * s3
  -- 5. substitute |AB| = 2·|AM| (line 4)
  have s5 : dist A B ^ 2 = (2 * dist A M) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s4
  -- 6. thm:pythagoras, from H5, H6
  have s6 : dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 := by exact (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := A) (B := B) (C := C) hH5 hH6)
  -- 7. algebra, from 2, 5, 6
  have s7 : dist C M ^ 2 = dist A M ^ 2 := by
    rw [dist_comm C A, dist_comm C B] at s2
    exact (by linear_combination (-(1 / 2 : ℝ)) * s2 + ((1 / 2 : ℝ)) * s5 + (-(1 / 2 : ℝ)) * s6)
  -- 8. mun:distance-nonneg P := C, Q := M
  have s8 : dist C M ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := C) (Q := M))
  -- 9. mun:distance-nonneg P := A, Q := M
  have s9 : dist A M ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := A) (Q := M))
  -- 10. mun:square-equal x := |CM|, y := |AM|, from 7, 8, 9
  have s10 : dist C M = dist A M := by exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := dist C M) (y := dist A M) s8 s9)).mp s7
  exact (by (have h := s10; rw [dist_comm C M, dist_comm A M] at h; exact h) : dist M C = dist M A)

end Parley.Proofs.Euclid.ThalesConverse.ThalesConverse
