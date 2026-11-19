module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
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
public import Mathlib.Data.Nat.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Stdlib.Geometry.CircleCentreApart

/-! Written from proofs/wiedijk/chords.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Chords.PowerOfAPoint

theorem power_of_a_point (A : ℂ) (B : ℂ) (P : ℂ) (O : ℂ) (hH5 : Sbtw ℝ A P B) (hH6 : dist A O = dist B O) :
    dist P A * dist P B = dist A O ^ 2 - dist P O ^ 2 := by
  -- 1. axi:excluded-middle P := O = P
  have s1 : O = P ∨ O ≠ P := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := O = P))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:distance-zero Q := O, from C1
    have s2_1 : dist P O = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := P) (Q := O))).mpr hC1.symm
    -- 2.2. substitute P = O (C1)
    have s2_2 : dist P A * dist P B = dist O A * dist O B := by (have h := congrArg (fun t : ℂ => (dist t A : ℂ) * (dist t B : ℂ)) hC1.symm; push_cast at h ⊢; exact_mod_cast h)
    -- 2.3. substitute |BO| = |AO| (H6) into line 2.2
    have s2_3 : dist P A * dist P B = dist A O * dist A O := by (have h := (by (have h := Eq.subst (motive := (fun t : ℝ => dist P A * dist P B = dist O A * t)) hH6.symm (by (have h := s2_2; rw [dist_comm O B] at h; exact h) : dist P A * dist P B = dist O A * dist B O); rw [dist_comm O A] at h; exact h) : dist P A * dist P B = dist A O * dist A O); push_cast at h ⊢; exact_mod_cast h)
    -- 2.4. algebra, from 2.1, 2.3
    linear_combination (dist P O) * s2_1 + s2_3
  · skip
    -- 2.5. mun:between-apart R := P, S := A, T := B, from H5
    have s2_5a : A ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := P) (S := A) (T := B) hH5)
    have s2_5b : B ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := P) (S := A) (T := B) hH5)
    -- 2.6. mun:circle-centre-apart X := A, Y := B, from H6
    have r55_1 : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := P) (S := A) (T := B) hH5)
    have s2_6 : A ≠ O := by exact (Parley.Stdlib.Geometry.CircleCentreApart.circle_centre_apart (X := A) (Y := B) (O := O) r55_1 hH6)
    -- 2.7. mun:circle-centre-apart X := B, Y := A, from H6
    have r59_1 : B ≠ A := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := P) (S := A) (T := B) hH5)
    have s2_7 : B ≠ O := by exact (Parley.Stdlib.Geometry.CircleCentreApart.circle_centre_apart (X := B) (Y := A) (O := O) r59_1 hH6.symm)
    -- 2.8. thm:law-of-cosines P := A, Q := P, R := O, from C2, 2.5, 2.6
    have s2_8 : dist O A ^ 2 = dist A P ^ 2 + dist P O ^ 2 - 2 * (dist A P * dist P O * Real.cos (EuclideanGeometry.angle A P O)) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_cosines (P := A) (Q := P) (R := O) s2_5a hC2 s2_6)
    -- 2.9. thm:law-of-cosines P := O, Q := P, R := B, from C2, 2.5, 2.7
    have s2_9 : dist B O ^ 2 = dist O P ^ 2 + dist P B ^ 2 - 2 * (dist O P * dist P B * Real.cos (EuclideanGeometry.angle O P B)) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_cosines (P := O) (Q := P) (R := B) hC2 s2_5b (Ne.symm s2_7))
    -- 2.10. axi:supplementary-angles B := P, C := B, D := O, from C2, H5, 2.6, 2.7
    have s2_10 : EuclideanGeometry.angle A P O + EuclideanGeometry.angle O P B = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := A) (B := P) (C := B) (D := O) hH5 hC2 (Ne.symm s2_6) (Ne.symm s2_7))
    -- 2.11. algebra, from 2.10
    have s2_11 : EuclideanGeometry.angle O P B = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P O := by linear_combination ((32400) / ((180) * (180))) * s2_10
    -- 2.12. calculation
    have s2_12 : Real.cos (EuclideanGeometry.angle O P B) = -Real.cos (EuclideanGeometry.angle A P O) := by
      calc Real.cos (EuclideanGeometry.angle O P B) = Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P O) := congrArg (fun t : ℝ => Real.cos t) s2_11
        _ = -Real.cos (EuclideanGeometry.angle A P O) := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_supplement (x := EuclideanGeometry.angle A P O))
    -- 2.13. substitute |BO| = |AO| (H6) into line 2.9
    have s2_13 : dist A O ^ 2 = dist P O ^ 2 + dist P B ^ 2 - 2 * (dist P O * dist P B * Real.cos (EuclideanGeometry.angle O P B)) := by (have h := (by (have h := Eq.subst (motive := (fun t : ℝ => t ^ 2 = dist O P ^ 2 + dist P B ^ 2 - 2 * (dist O P * dist P B * Real.cos (EuclideanGeometry.angle O P B)))) hH6.symm s2_9; rw [dist_comm O P] at h; exact h) : dist A O ^ 2 = dist P O ^ 2 + dist P B ^ 2 - 2 * (dist P O * dist P B * Real.cos (EuclideanGeometry.angle O P B))); push_cast at h ⊢; exact_mod_cast h)
    -- 2.14. substitute cos(∠OPB) = −cos(∠APO) (line 2.12) into line 2.13
    have s2_14 : dist A O ^ 2 = dist P O ^ 2 + dist P B ^ 2 - 2 * (dist P O * dist P B * -Real.cos (EuclideanGeometry.angle A P O)) := Eq.subst (motive := (fun t : ℝ => dist A O ^ 2 = dist P O ^ 2 + dist P B ^ 2 - 2 * (dist P O * dist P B * t))) s2_12 s2_13
    -- 2.15. axi:distance-positive Q := A, from 2.5
    have s2_15 : dist P A > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P) (Q := A) (Ne.symm s2_5a))
    -- 2.16. axi:distance-positive Q := B, from 2.5
    have s2_16 : dist P B > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P) (Q := B) (Ne.symm s2_5b))
    -- 2.17. calculation
    have r92_1 : dist P A ≠ 0 := ne_of_gt (by linarith only [s2_15])
    have r92_2 : dist P B ≠ 0 := ne_of_gt (by linarith only [s2_16])
    have s2_17 : (dist P A ^ 2 + dist P O ^ 2 - dist A O ^ 2) / dist P A = (dist A O ^ 2 - dist P O ^ 2 - dist P B ^ 2) / dist P B := by
      calc (dist P A ^ 2 + dist P O ^ 2 - dist A O ^ 2) / dist P A = 2 * (dist P O * Real.cos (EuclideanGeometry.angle A P O)) := by
            rw [dist_comm O A, dist_comm P O] at s2_8
            rw [dist_comm P A, dist_comm P O]
            exact (by have hz1 : dist A P ≠ 0 := (by (have h := r92_1; rw [dist_comm P A] at h; exact h) : dist A P ≠ 0); linear_combination (norm := (field)) ((-1) / ((dist A P))) * s2_8)
        _ = (dist A O ^ 2 - dist P O ^ 2 - dist P B ^ 2) / dist P B := by have hz1 : dist P B ≠ 0 := r92_2; linear_combination (norm := (field)) ((-1) / ((dist P B))) * s2_14
    -- 2.18. algebra, from 2.17
    have r99_1 : dist P A ≠ 0 := ne_of_gt (by linarith only [s2_15])
    have r99_2 : dist P B ≠ 0 := ne_of_gt (by linarith only [s2_16])
    have s2_18 : dist P A * dist P B * (dist P A + dist P B) = (dist A O ^ 2 - dist P O ^ 2) * (dist P A + dist P B) := by have hz1 : dist P A ≠ 0 := r99_1; have hz2 : dist P B ≠ 0 := r99_2; linear_combination (norm := (field)) (dist P A * dist P B) * s2_17
    -- 2.19. inequalities, from 2.15, 2.16
    have s2_19 : dist P A + dist P B > 0 := by linarith only [s2_15, s2_16]
    -- 2.20. mun:multiply-cancel a := |PA|·|PB|, b := |AO|² − |PO|², c := |PA| + |PB|, from 2.18
    have r107_1 : dist P A + dist P B ≠ 0 := ne_of_gt (by linarith only [s2_19])
    exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := dist P A * dist P B) (b := dist A O ^ 2 - dist P O ^ 2) (c := dist P A + dist P B) s2_18 r107_1)

end Parley.Proofs.Wiedijk.Chords.PowerOfAPoint
