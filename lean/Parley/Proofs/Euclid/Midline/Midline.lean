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
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Euclid.Apollonius.Apollonius

/-! Written from proofs/euclid/midline.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.Midline.Midline

theorem midline (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (N : ℂ) (hH6 : Sbtw ℝ A M B ∧ dist A M = dist M B) (hH7 : Sbtw ℝ A N C ∧ dist A N = dist N C) :
    dist M N = dist B C / 2 := by
  -- 1. def:midpoint, from H6
  have s1a : Sbtw ℝ A M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH6).1
  have s1b : dist A M = dist M B := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := B) (M := M))).mp hH6).2
  -- 2. def:midpoint M := N, B := C, from H7
  have s2a : Sbtw ℝ A N C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := C) (M := N))).mp hH7).1
  have s2b : dist A N = dist N C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := C) (M := N))).mp hH7).2
  -- 3. mun:segment-addition P := A, Q := B, S := M, from 1
  have s3 : dist A M + dist M B = dist A B := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := B) (S := M) s1a)
  -- 4. algebra, from 1, 3
  have s4 : dist A M = dist A B / 2 := by linear_combination ((1) / (((2 : ℝ)))) * s1b + ((1) / (((2 : ℝ)))) * s3
  -- 5. thm:apollonius A := B, B := A, M := N, from 2
  have s5 : dist B A ^ 2 + dist B C ^ 2 = 2 * dist B N ^ 2 + 2 * dist A N ^ 2 := by exact (Parley.Proofs.Euclid.Apollonius.Apollonius.apollonius (A := B) (B := A) (C := C) (M := N) s2a s2b)
  -- 6. thm:apollonius A := N, B := A, C := B, from 1
  have s6 : dist N A ^ 2 + dist N B ^ 2 = 2 * dist N M ^ 2 + 2 * dist A M ^ 2 := by exact (Parley.Proofs.Euclid.Apollonius.Apollonius.apollonius (A := N) (B := A) (C := B) (M := M) s1a s1b)
  -- 7. substitute |AM| = |AB|/2 (line 4) into line 6
  have s7 : dist A N ^ 2 + dist B N ^ 2 = 2 * dist N M ^ 2 + 2 * (dist A B / 2) ^ 2 := by (have h := (by (have h := Eq.subst (motive := (fun t : ℝ => dist N A ^ 2 + dist N B ^ 2 = 2 * dist N M ^ 2 + 2 * t ^ 2)) s4 s6; rw [dist_comm N A, dist_comm N B] at h; exact h) : dist A N ^ 2 + dist B N ^ 2 = 2 * dist N M ^ 2 + 2 * (dist A B / 2) ^ 2); push_cast at h ⊢; exact_mod_cast h)
  -- 8. algebra, from 5, 7
  have s8 : dist N M ^ 2 = (dist B C / 2) ^ 2 := by
    rw [dist_comm B A] at s5
    rw [dist_comm N M] at s7
    rw [dist_comm N M]
    exact (by linear_combination ((-1) / ((4))) * s5 + ((-8) / ((4) * (4))) * s7)
  -- 9. mun:distance-nonneg P := N, Q := M
  have s9 : dist N M ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := N) (Q := M))
  -- 10. mun:distance-nonneg P := B, Q := C
  have s10 : dist B C ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := B) (Q := C))
  -- 11. inequalities
  have s11 : dist B C / 2 ≥ 0 := by linarith only [s10]
  -- 12. mun:square-equal x := |NM|, y := |BC|/2, from 8, 9, 11
  have s12 : dist N M = dist B C / 2 := by exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := dist N M) (y := dist B C / 2) s9 s11)).mp s8
  exact (by (have h := s12; rw [dist_comm N M] at h; exact h) : dist M N = dist B C / 2)

end Parley.Proofs.Euclid.Midline.Midline
