module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.ExteriorAngleGreater
public import Parley.Stdlib.Geometry.ExteriorAngleGreaterOther
public import Parley.Stdlib.Geometry.PerpendicularFoot

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AltitudeFoot

theorem altitude_foot (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) (hH5 : EuclideanGeometry.angle P R Q = (90 : ℝ) * Real.pi / 180) :
    (∃ D ∈ (Set.univ : Set ℂ), (((Sbtw ℝ P D Q ∧ LeanBridges.Geometry.Triangle P D R) ∧ LeanBridges.Geometry.Triangle Q D R) ∧ EuclideanGeometry.angle P D R = (90 : ℝ) * Real.pi / 180) ∧ EuclideanGeometry.angle Q D R = (90 : ℝ) * Real.pi / 180) := by
  -- 1. axi:distance-positive P := Q, Q := R, from H4
  have s1 : dist Q R > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := Q) (Q := R) hH4.2.1)
  -- 2. obtain Y: mun:segment-extension A := Q, B := R, r := |QR|, from H4, 1
  obtain ⟨Y, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := Q) (B := R) (r := dist Q R) hH4.2.1 s1)
  -- 3. mun:triangle-extension Q := R, R := Q, S := Y, from H4, 2
  have s3 : LeanBridges.Geometry.Triangle P R Y := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := P) (Q := R) (R := Q) (S := Y) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle P R Q) s2b)
  -- 4. axi:supplementary-angles A := Q, B := R, C := Y, D := P, from H4, 2, 3
  have s4 : EuclideanGeometry.angle Q R P + EuclideanGeometry.angle P R Y = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := Q) (B := R) (C := Y) (D := P) s2b hH4.2.2.1 hH4.1 s3.2.2.1)
  -- 5. mun:angle-turned Q := R, R := Q, from H4
  have s5 : EuclideanGeometry.angle P R Q = EuclideanGeometry.angle Q R P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := R) (R := Q) hH4.2.2.1 hH4.2.1 hH4.1)
  -- 6. thm:exterior-angle-greater A := P, B := Q, C := R, D := Y, from H4, 2, 3
  have s6 : EuclideanGeometry.angle P R Y > EuclideanGeometry.angle Q P R := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreater.exterior_angle_greater (A := P) (B := Q) (C := R) (D := Y) hH4 s2b s3)
  -- 7. substitute
  have s7 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle Q P R := by
    have c1 : EuclideanGeometry.angle P R Y = (90 : ℝ) * Real.pi / 180 := by linear_combination ((-32400) / ((180) * (180))) * hH5 + ((32400) / ((180) * (180))) * s4 + ((180) / ((180))) * s5
    have row1 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle Q P R := Eq.subst (motive := (fun t : ℝ => t > EuclideanGeometry.angle Q P R)) c1 s6
    exact row1
  -- 8. substitute
  have s8 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle R P Q := by
    have c1 : EuclideanGeometry.angle Q P R = EuclideanGeometry.angle R P Q := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := Q) (Q := P) (R := R) (Ne.symm hH4.1) (Ne.symm hH4.2.2.1) hH4.2.1)
    have row1 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle R P Q := Eq.subst (motive := (fun t : ℝ => (90 : ℝ) * Real.pi / 180 > t)) c1 s7
    exact row1
  -- 9. axi:distance-positive Q := R, from H4
  have s9 : dist P R > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P) (Q := R) hH4.2.2.1)
  -- 10. obtain Z: mun:segment-extension A := P, B := R, r := |PR|, from H4, 9
  obtain ⟨Z, s10a, ⟨s10b, s10c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := P) (B := R) (r := dist P R) hH4.2.2.1 s9)
  -- 11. mun:triangle-extension P := Q, Q := R, R := P, S := Z, from H4, 10
  have s11 : LeanBridges.Geometry.Triangle Q R Z := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := Q) (Q := R) (R := P) (S := Z) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q R P) s10b)
  -- 12. axi:supplementary-angles A := P, B := R, C := Z, D := Q, from H4, 10, 11
  have s12 : EuclideanGeometry.angle P R Q + EuclideanGeometry.angle Q R Z = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := P) (B := R) (C := Z) (D := Q) s10b hH4.2.1 (Ne.symm hH4.1) s11.2.2.1)
  -- 13. thm:exterior-angle-greater A := Q, B := P, C := R, D := Z, from H4, 10, 11
  have s13 : EuclideanGeometry.angle Q R Z > EuclideanGeometry.angle P Q R := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreater.exterior_angle_greater (A := Q) (B := P) (C := R) (D := Z) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle Q P R) s10b s11)
  -- 14. substitute
  have s14 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle P Q R := by
    have c1 : EuclideanGeometry.angle Q R Z = (90 : ℝ) * Real.pi / 180 := by linear_combination ((-32400) / ((180) * (180))) * hH5 + ((32400) / ((180) * (180))) * s12
    have row1 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle P Q R := Eq.subst (motive := (fun t : ℝ => t > EuclideanGeometry.angle P Q R)) c1 s13
    exact row1
  -- 15. substitute
  have s15 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle R Q P := by
    have c1 : EuclideanGeometry.angle P Q R = EuclideanGeometry.angle R Q P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := Q) (R := R) hH4.1 (Ne.symm hH4.2.1) hH4.2.2.1)
    have row1 : (90 : ℝ) * Real.pi / 180 > EuclideanGeometry.angle R Q P := Eq.subst (motive := (fun t : ℝ => (90 : ℝ) * Real.pi / 180 > t)) c1 s14
    exact row1
  -- 16. obtain D: thm:perpendicular-foot P := R, Q := P, R := Q, from H4
  obtain ⟨D, s16a, ⟨⟨⟨s16b, s16c⟩, s16d⟩, s16e⟩⟩ := (Parley.Stdlib.Geometry.PerpendicularFoot.perpendicular_foot (P := R) (Q := P) (R := Q) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_312 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle R P Q))
  -- 17. mun:on-line-cases P := D, Q := P, R := Q, from H4, 16
  have s17 : (((D = P ∨ Sbtw ℝ P D Q) ∨ D = Q) ∨ Sbtw ℝ P Q D) ∨ Sbtw ℝ D P Q := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := D) (Q := P) (R := Q) hH4.1 s16b)
  -- 18. cases, from 17
  have s18 : Sbtw ℝ P D Q := by
    rcases s17 with (((hC1 | hC2) | hC3) | hC4) | hC5
    · skip
      -- 18.1. contradiction
      have s18_1 : D ≠ Q := by
        intro hS1
        -- 18.1.1. transitivity, from C1, S1
        have s18_1_1 : P = Q := by exact Eq.trans hC1.symm hS1
        -- 18.1.2. def:triangle, from H4
        have s18_1_2 : P ≠ Q := by exact (((Parley.Items.Stdlib.Geometry.def_triangle (P := P) (Q := Q) (R := R))).mp hH4).1.1.1
        exact s18_1_2 s18_1_1
      -- 18.2. mun:modus-ponens, from 16, 18.1
      have s18_2 : EuclideanGeometry.angle R D Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := D ≠ Q) (Q := EuclideanGeometry.angle R D Q = (90 : ℝ) * Real.pi / 180) s16e s18_1)
      -- 18.3. substitute D = P (C1) into line 18.2
      have s18_3 : EuclideanGeometry.angle R P Q = (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle R t Q = (90 : ℝ) * Real.pi / 180)) hC1 s18_2
      -- 18.4. substitute ∠RPQ = 90° (line 18.3) into line 8
      have s18_4 : (90 : ℝ) * Real.pi / 180 > (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℝ => (90 : ℝ) * Real.pi / 180 > t)) s18_3 s8
      exact absurd s18_4 (by norm_num)
    · skip
      exact hC2
    · skip
      -- 18.5. contradiction
      have s18_5 : D ≠ P := by
        intro hS2
        -- 18.5.1. transitivity, from C3, S2
        have s18_5_1 : P = Q := by exact (Eq.trans hC3.symm hS2).symm
        -- 18.5.2. def:triangle, from H4
        have s18_5_2 : P ≠ Q := by exact (((Parley.Items.Stdlib.Geometry.def_triangle (P := P) (Q := Q) (R := R))).mp hH4).1.1.1
        exact s18_5_2 s18_5_1
      -- 18.6. mun:modus-ponens, from 16, 18.5
      have s18_6 : EuclideanGeometry.angle R D P = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := D ≠ P) (Q := EuclideanGeometry.angle R D P = (90 : ℝ) * Real.pi / 180) s16d s18_5)
      -- 18.7. substitute D = Q (C3) into line 18.6
      have s18_7 : EuclideanGeometry.angle R Q P = (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℂ => EuclideanGeometry.angle R t P = (90 : ℝ) * Real.pi / 180)) hC3 s18_6
      -- 18.8. substitute ∠RQP = 90° (line 18.7) into line 15
      have s18_8 : (90 : ℝ) * Real.pi / 180 > (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℝ => (90 : ℝ) * Real.pi / 180 > t)) s18_7 s15
      exact absurd s18_8 (by norm_num)
    · skip
      -- 18.9. mun:between-apart R := Q, S := P, T := D, from C4
      have s18_9a : P ≠ Q := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := Q) (S := P) (T := D) hC4)
      have s18_9b : D ≠ Q := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := Q) (S := P) (T := D) hC4)
      -- 18.10. mun:modus-ponens, from 16, 18.9
      have s18_10 : EuclideanGeometry.angle R D Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := D ≠ Q) (Q := EuclideanGeometry.angle R D Q = (90 : ℝ) * Real.pi / 180) s16e s18_9b)
      -- 18.11. mun:right-angle-triangle P := R, Q := D, R := Q, from H4, 16, 18.9, 18.10
      have s18_11 : LeanBridges.Geometry.Triangle R D Q := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := R) (Q := D) (R := Q) s16c (Ne.symm s18_9b) s18_10 (Ne.symm hH4.2.1))
      -- 18.12. thm:exterior-angle-greater-other A := R, B := D, C := Q, D := P, from C4, 18.11
      have r1567_1 : LeanBridges.Geometry.Triangle R Q P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := R) (Q := Q) (R := D) (S := P) (by (have h := s18_11; rw [LeanBridges.Geometry.triangle_swap_23 R D Q] at h; exact h) : LeanBridges.Geometry.Triangle R Q D) (by (have h := hC4; rw [sbtw_comm (x := P) (y := Q) (z := D)] at h; exact h) : Sbtw ℝ D Q P))
      have s18_12 : EuclideanGeometry.angle R Q P > EuclideanGeometry.angle R D Q := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreaterOther.exterior_angle_greater_other (A := R) (B := D) (C := Q) (D := P) s18_11 (by (have h := hC4; rw [sbtw_comm (x := P) (y := Q) (z := D)] at h; exact h) : Sbtw ℝ D Q P) r1567_1)
      -- 18.13. substitute ∠RDQ = 90° (line 18.10) into line 18.12
      have s18_13 : EuclideanGeometry.angle R Q P > (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℝ => EuclideanGeometry.angle R Q P > t)) s18_10 s18_12
      -- 18.14. transitivity, from 18.13, 15
      have s18_14 : EuclideanGeometry.angle R Q P > EuclideanGeometry.angle R Q P := by exact lt_trans s15 s18_13
      -- 18.15. inequalities
      have s18_15 : (0 : ℝ) > 0 := by exact_mod_cast (show (0 : ℝ) > 0 by linarith only [s18_14])
      exact absurd s18_15 (by norm_num)
    · skip
      -- 18.16. mun:between-apart R := P, S := D, T := Q, from C5
      have s18_16a : D ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := P) (S := D) (T := Q) hC5)
      have s18_16b : Q ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := P) (S := D) (T := Q) hC5)
      -- 18.17. mun:modus-ponens, from 16, 18.16
      have s18_17 : EuclideanGeometry.angle R D P = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := D ≠ P) (Q := EuclideanGeometry.angle R D P = (90 : ℝ) * Real.pi / 180) s16d s18_16a)
      -- 18.18. mun:right-angle-triangle P := R, Q := D, R := P, from H4, 16, 18.16, 18.17
      have s18_18 : LeanBridges.Geometry.Triangle R D P := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := R) (Q := D) (R := P) s16c (Ne.symm s18_16a) s18_17 (Ne.symm hH4.2.2.1))
      -- 18.19. thm:exterior-angle-greater-other A := R, B := D, C := P, D := Q, from C5, 18.18
      have r1596_1 : LeanBridges.Geometry.Triangle R P Q := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := R) (Q := P) (R := D) (S := Q) (by (have h := s18_18; rw [LeanBridges.Geometry.triangle_swap_23 R D P] at h; exact h) : LeanBridges.Geometry.Triangle R P D) hC5)
      have s18_19 : EuclideanGeometry.angle R P Q > EuclideanGeometry.angle R D P := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreaterOther.exterior_angle_greater_other (A := R) (B := D) (C := P) (D := Q) s18_18 hC5 r1596_1)
      -- 18.20. substitute ∠RDP = 90° (line 18.17) into line 18.19
      have s18_20 : EuclideanGeometry.angle R P Q > (90 : ℝ) * Real.pi / 180 := Eq.subst (motive := (fun t : ℝ => EuclideanGeometry.angle R P Q > t)) s18_17 s18_19
      -- 18.21. transitivity, from 18.20, 8
      have s18_21 : EuclideanGeometry.angle R P Q > EuclideanGeometry.angle R P Q := by exact lt_trans s8 s18_20
      -- 18.22. inequalities
      have s18_22 : (0 : ℝ) > 0 := by exact_mod_cast (show (0 : ℝ) > 0 by linarith only [s18_21])
      exact absurd s18_22 (by norm_num)
  -- 19. mun:between-apart R := D, S := P, T := Q, from 18
  have s19a : P ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := D) (S := P) (T := Q) s18)
  have s19b : Q ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := D) (S := P) (T := Q) s18)
  -- 20. mun:modus-ponens, from 16, 19
  have s20 : EuclideanGeometry.angle R D P = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := D ≠ P) (Q := EuclideanGeometry.angle R D P = (90 : ℝ) * Real.pi / 180) s16d (Ne.symm s19a))
  -- 21. mun:modus-ponens, from 16, 19
  have s21 : EuclideanGeometry.angle R D Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := D ≠ Q) (Q := EuclideanGeometry.angle R D Q = (90 : ℝ) * Real.pi / 180) s16e (Ne.symm s19b))
  -- 22. mun:angle-turned Q := D, from H4, 16, 19
  have s22 : EuclideanGeometry.angle P D R = EuclideanGeometry.angle R D P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := D) (R := R) s19a s16c hH4.2.2.1)
  -- 23. transitivity, from 22, 20
  have s23 : EuclideanGeometry.angle P D R = (90 : ℝ) * Real.pi / 180 := by exact Eq.trans s22 s20
  -- 24. mun:angle-turned P := Q, Q := D, from H4, 16, 19
  have s24 : EuclideanGeometry.angle Q D R = EuclideanGeometry.angle R D Q := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := Q) (Q := D) (R := R) s19b s16c hH4.2.1)
  -- 25. transitivity, from 24, 21
  have s25 : EuclideanGeometry.angle Q D R = (90 : ℝ) * Real.pi / 180 := by exact Eq.trans s24 s21
  -- 26. mun:right-angle-triangle Q := D, from H4, 16, 19, 23
  have s26 : LeanBridges.Geometry.Triangle P D R := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := P) (Q := D) (R := R) s19a s16c s23 hH4.2.2.1)
  -- 27. mun:right-angle-triangle P := Q, Q := D, from H4, 16, 19, 25
  have s27 : LeanBridges.Geometry.Triangle Q D R := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := Q) (Q := D) (R := R) s19b s16c s25 hH4.2.1)
  -- 28. exhibit, from 18, 23, 25, 26, 27
  exact ⟨D, Set.mem_univ _, ⟨⟨⟨⟨s18, s26⟩, s27⟩, s23⟩, s25⟩⟩

end Parley.Stdlib.Geometry.AltitudeFoot
