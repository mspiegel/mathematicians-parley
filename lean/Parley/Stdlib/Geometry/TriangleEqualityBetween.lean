module

public import Geometry
public import Batteries.Tactic.Init
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
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.TriangleInequalityStrict

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.TriangleEqualityBetween

theorem triangle_equality_between (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : P ≠ Q) (hH5 : Q ≠ R) (hH6 : dist P Q + dist Q R = dist P R) :
    Sbtw ℝ P Q R := by
  -- 1. axi:distance-positive, from H4
  have s1 : dist P Q > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P) (Q := Q) hH4)
  -- 2. axi:distance-positive P := Q, Q := R, from H5
  have s2 : dist Q R > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := Q) (Q := R) hH5)
  -- 3. contradiction
  have s3 : P ≠ R := by
    intro hS
    -- 3.1. inequalities, from 1, 2
    have s3_1 : dist P Q + dist Q R > 0 := by linarith only [s1, s2]
    -- 3.2. substitute |PQ| + |QR| = |PR| (H6) into line 3.1
    have s3_2 : dist P R > 0 := Eq.subst (motive := (fun t : ℝ => t > 0)) hH6 s3_1
    -- 3.3. substitute
    have s3_3 : (0 : ℝ) > 0 := by
      have c1 : dist P R = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := P) (Q := R))).mpr hS
      have row1 : (0 : ℝ) > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t > 0)) c1 s3_2; revert h; norm_num)
      exact row1
    exact absurd s3_3 (by norm_num)
  -- 4. contradiction
  have s4 : Q ∈ LeanBridges.Geometry.line P R := by
    by_contra hS
    -- 4.1. mun:triangle-off-line P := Q, Q := P, from S, 3
    have s4_1 : LeanBridges.Geometry.Triangle Q P R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := Q) (Q := P) (R := R) s3 hS)
    -- 4.2. thm:triangle-inequality-strict, from 4.1
    have s4_2 : dist P R < dist P Q + dist Q R := by exact (Parley.Stdlib.Geometry.TriangleInequalityStrict.triangle_inequality_strict (P := P) (Q := Q) (R := R) (by (have h := s4_1; rw [LeanBridges.Geometry.triangle_swap_12 Q P R] at h; exact h) : LeanBridges.Geometry.Triangle P Q R))
    -- 4.3. substitute |PQ| + |QR| = |PR| (H6) into line 4.2
    have s4_3 : dist P R < dist P R := Eq.subst (motive := (fun t : ℝ => dist P R < t)) hH6 s4_2
    -- 4.4. inequalities
    have s4_4 : (0 : ℝ) < 0 := by exact_mod_cast (show (0 : ℝ) < 0 by linarith only [s4_3])
    exact absurd s4_4 (by norm_num)
  -- 5. mun:on-line-cases P := Q, Q := P, from 3, 4
  have s5 : (((Q = P ∨ Sbtw ℝ P Q R) ∨ Q = R) ∨ Sbtw ℝ P R Q) ∨ Sbtw ℝ Q P R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := Q) (Q := P) (R := R) s3 s4)
  -- 6. cases, from 5
  rcases s5 with (((hC1 | hC2) | hC3) | hC4) | hC5
  · skip
    -- 6.1. restate H4
    have s6_1 : P ≠ Q := by exact hH4
    exact absurd hC1.symm s6_1
  · skip
    exact hC2
  · skip
    -- 6.2. restate H5
    have s6_2 : Q ≠ R := by exact hH5
    exact absurd hC3 s6_2
  · skip
    -- 6.3. mun:segment-addition S := R, from C4
    have s6_3 : dist P R + dist R Q = dist P Q := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := P) (Q := Q) (S := R) hC4)
    -- 6.4. substitute
    have s6_4 : (0 : ℝ) > 0 := by
      have c1 : dist Q R = 0 := by
        rw [dist_comm R Q] at s6_3
        exact (by linear_combination ((1 / 2 : ℝ)) * hH6 + ((1 / 2 : ℝ)) * s6_3)
      have row1 : (0 : ℝ) > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t > 0)) c1 s2; revert h; norm_num)
      exact row1
    exact absurd s6_4 (by norm_num)
  · skip
    -- 6.5. mun:segment-addition P := Q, Q := R, S := P, from C5
    have s6_5 : dist Q P + dist P R = dist Q R := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := Q) (Q := R) (S := P) hC5)
    -- 6.6. substitute
    have s6_6 : (0 : ℝ) > 0 := by
      have c1 : dist P Q = 0 := by
        rw [dist_comm Q P] at s6_5
        exact (by linear_combination ((1 / 2 : ℝ)) * hH6 + ((1 / 2 : ℝ)) * s6_5)
      have row1 : (0 : ℝ) > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t > 0)) c1 s1; revert h; norm_num)
      exact row1
    exact absurd s6_6 (by norm_num)

end Parley.Stdlib.Geometry.TriangleEqualityBetween
