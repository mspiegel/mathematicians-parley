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
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Euclid.Apollonius.Apollonius

/-! Written from proofs/euclid/parallelogram-law.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ParallelogramLaw.ParallelogramLaw

theorem parallelogram_law (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (M : ℂ) (hH6 : Sbtw ℝ A M C ∧ dist A M = dist M C) (hH7 : Sbtw ℝ B M D ∧ dist B M = dist M D) :
    dist A C ^ 2 + dist B D ^ 2 = 2 * dist A B ^ 2 + 2 * dist B C ^ 2 := by
  -- 1. def:midpoint B := C, from H6
  have s1a : Sbtw ℝ A M C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := C) (M := M))).mp hH6).1
  have s1b : dist A M = dist M C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := C) (M := M))).mp hH6).2
  -- 2. def:midpoint A := B, B := D, from H7
  have s2a : Sbtw ℝ B M D := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := B) (B := D) (M := M))).mp hH7).1
  have s2b : dist B M = dist M D := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := B) (B := D) (M := M))).mp hH7).2
  -- 3. thm:apollonius A := B, B := A, from 1
  have s3 : dist B A ^ 2 + dist B C ^ 2 = 2 * dist B M ^ 2 + 2 * dist A M ^ 2 := by exact (Parley.Proofs.Euclid.Apollonius.Apollonius.apollonius (A := B) (B := A) (C := C) (M := M) s1a s1b)
  -- 4. mun:segment-addition P := A, Q := C, S := M, from 1
  have s4 : dist A M + dist M C = dist A C := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := C) (S := M) s1a)
  -- 5. mun:segment-addition P := B, Q := D, S := M, from 2
  have s5 : dist B M + dist M D = dist B D := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := B) (Q := D) (S := M) s2a)
  -- 6. algebra, from 1, 4
  have s6 : dist A C = 2 * dist A M := by linear_combination (-1) * s1b + (-1) * s4
  -- 7. algebra, from 2, 5
  have s7 : dist B D = 2 * dist B M := by linear_combination (-1) * s2b + (-1) * s5
  -- 8. substitute |AC| = 2·|AM| (line 6)
  have s8 : dist A C ^ 2 = (2 * dist A M) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s6
  -- 9. substitute |BD| = 2·|BM| (line 7)
  have s9 : dist B D ^ 2 = (2 * dist B M) ^ 2 := congrArg (fun t : ℝ => t ^ 2) s7
  -- 10. algebra, from 3, 8, 9
  rw [dist_comm B A] at s3
  exact (by linear_combination (-2) * s3 + s8 + s9)

end Parley.Proofs.Euclid.ParallelogramLaw.ParallelogramLaw
