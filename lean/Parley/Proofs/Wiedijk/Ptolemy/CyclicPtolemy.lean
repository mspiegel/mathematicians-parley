module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
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
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Stdlib.Geometry.IntersectingChords

/-! Written from proofs/wiedijk/ptolemy.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ptolemy.CyclicPtolemy

theorem cyclic_ptolemy (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (O : ℂ) (P : ℂ) (hH7 : dist A O = dist B O) (hH8 : dist A O = dist C O) (hH9 : dist A O = dist D O) (hH10 : Sbtw ℝ A P C) (hH11 : Sbtw ℝ B P D) (hH12 : A ≠ B) (hH13 : B ≠ C) (hH14 : C ≠ D) (hH15 : D ≠ A) :
    dist A C * dist B D = dist A B * dist C D + dist A D * dist B C := by
  -- 1. mun:between-apart R := P, S := A, T := C, from H10
  have s1a : A ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := P) (S := A) (T := C) hH10)
  have s1b : C ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := P) (S := A) (T := C) hH10)
  -- 2. mun:between-apart R := P, S := B, T := D, from H11
  have s2a : B ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := P) (S := B) (T := D) hH11)
  have s2b : D ≠ P := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := P) (S := B) (T := D) hH11)
  -- 3. thm:intersecting-chords B := C, C := B, from H7, H8, H9, H10, H11
  have s3 : dist P A * dist P C = dist P B * dist P D := by exact (Parley.Stdlib.Geometry.IntersectingChords.intersecting_chords (A := A) (B := C) (C := B) (D := D) (P := P) (O := O) hH10 hH11 hH8 hH7 hH9)
  -- 4. axi:supplementary-angles B := P, D := B, from H10, H12, H13, 2
  have s4 : EuclideanGeometry.angle A P B + EuclideanGeometry.angle B P C = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := A) (B := P) (C := C) (D := B) hH10 s2a (Ne.symm hH12) hH13)
  -- 5. axi:supplementary-angles A := B, B := P, C := D, D := C, from H11, H13, H14, 1
  have s5 : EuclideanGeometry.angle B P C + EuclideanGeometry.angle C P D = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := B) (B := P) (C := D) (D := C) hH11 s1b (Ne.symm hH13) hH14)
  -- 6. axi:supplementary-angles A := C, B := P, C := A, from H10, H14, H15, 2
  have s6 : EuclideanGeometry.angle C P D + EuclideanGeometry.angle D P A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := C) (B := P) (C := A) (D := D) (by (have h := hH10; rw [sbtw_comm (x := A) (y := P) (z := C)] at h; exact h) : Sbtw ℝ C P A) s2b (Ne.symm hH14) hH15)
  -- 7. algebra, from 4, 5
  have s7 : EuclideanGeometry.angle C P D = EuclideanGeometry.angle A P B := by linear_combination ((-180) / ((180))) * s4 + ((180) / ((180))) * s5
  -- 8. mun:cos-supplement x := ∠APB
  have s8 : Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P B) = -Real.cos (EuclideanGeometry.angle A P B) := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_supplement (x := EuclideanGeometry.angle A P B))
  set c : ℝ := Real.cos (EuclideanGeometry.angle A P B) with hD1
  -- 9. thm:law-of-cosines P := A, Q := P, R := B, from H12, 1, 2
  have s9 : dist B A ^ 2 = dist A P ^ 2 + dist P B ^ 2 - 2 * (dist A P * dist P B * Real.cos (EuclideanGeometry.angle A P B)) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_cosines (P := A) (Q := P) (R := B) s1a s2a hH12)
  -- 10. thm:law-of-cosines P := B, Q := P, R := C, from H13, 1, 2
  have s10 : dist C B ^ 2 = dist B P ^ 2 + dist P C ^ 2 - 2 * (dist B P * dist P C * Real.cos (EuclideanGeometry.angle B P C)) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_cosines (P := B) (Q := P) (R := C) s2a s1b hH13)
  -- 11. substitute
  have s11 : dist C B ^ 2 = dist B P ^ 2 + dist P C ^ 2 - 2 * (dist B P * dist P C * -Real.cos (EuclideanGeometry.angle A P B)) := by
    have c1 : EuclideanGeometry.angle B P C = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P B := by linear_combination ((32400) / ((180) * (180))) * s4
    have row1 : dist C B ^ 2 = dist B P ^ 2 + dist P C ^ 2 - 2 * (dist B P * dist P C * Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P B)) := Eq.subst (motive := (fun t : ℝ => dist C B ^ 2 = dist B P ^ 2 + dist P C ^ 2 - 2 * (dist B P * dist P C * Real.cos t))) c1 s10
    have c2 : Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P B) = -Real.cos (EuclideanGeometry.angle A P B) := congrArg (fun t : ℝ => t) s8
    have row2 : dist C B ^ 2 = dist B P ^ 2 + dist P C ^ 2 - 2 * (dist B P * dist P C * -Real.cos (EuclideanGeometry.angle A P B)) := Eq.subst (motive := (fun t : ℝ => dist C B ^ 2 = dist B P ^ 2 + dist P C ^ 2 - 2 * (dist B P * dist P C * t))) c2 row1
    exact row2
  -- 12. thm:law-of-cosines P := C, Q := P, R := D, from H14, 1, 2
  have s12 : dist D C ^ 2 = dist C P ^ 2 + dist P D ^ 2 - 2 * (dist C P * dist P D * Real.cos (EuclideanGeometry.angle C P D)) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_cosines (P := C) (Q := P) (R := D) s1b s2b hH14)
  -- 13. substitute ∠CPD = ∠APB (line 7) into line 12
  have s13 : dist D C ^ 2 = dist C P ^ 2 + dist P D ^ 2 - 2 * (dist C P * dist P D * Real.cos (EuclideanGeometry.angle A P B)) := Eq.subst (motive := (fun t : ℝ => dist D C ^ 2 = dist C P ^ 2 + dist P D ^ 2 - 2 * (dist C P * dist P D * Real.cos t))) s7 s12
  -- 14. thm:law-of-cosines P := D, Q := P, R := A, from H15, 1, 2
  have s14 : dist A D ^ 2 = dist D P ^ 2 + dist P A ^ 2 - 2 * (dist D P * dist P A * Real.cos (EuclideanGeometry.angle D P A)) := by exact (Parley.Items.Stdlib.Geometry.thm_law_of_cosines (P := D) (Q := P) (R := A) s2b s1a hH15)
  -- 15. substitute
  have s15 : dist A D ^ 2 = dist D P ^ 2 + dist P A ^ 2 - 2 * (dist D P * dist P A * -Real.cos (EuclideanGeometry.angle A P B)) := by
    have c1 : EuclideanGeometry.angle D P A = (180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P B := by linear_combination ((32400) / ((180) * (180))) * s6 + ((-180) / ((180))) * s7
    have row1 : dist A D ^ 2 = dist D P ^ 2 + dist P A ^ 2 - 2 * (dist D P * dist P A * Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P B)) := Eq.subst (motive := (fun t : ℝ => dist A D ^ 2 = dist D P ^ 2 + dist P A ^ 2 - 2 * (dist D P * dist P A * Real.cos t))) c1 s14
    have c2 : Real.cos ((180 : ℝ) * Real.pi / 180 - EuclideanGeometry.angle A P B) = -Real.cos (EuclideanGeometry.angle A P B) := congrArg (fun t : ℝ => t) s8
    have row2 : dist A D ^ 2 = dist D P ^ 2 + dist P A ^ 2 - 2 * (dist D P * dist P A * -Real.cos (EuclideanGeometry.angle A P B)) := Eq.subst (motive := (fun t : ℝ => dist A D ^ 2 = dist D P ^ 2 + dist P A ^ 2 - 2 * (dist D P * dist P A * t))) c2 row1
    exact row2
  -- 16. algebra, from 3
  have s16 : (dist P A * dist P C) ^ 2 = (dist P B * dist P D) ^ 2 := by linear_combination (dist P A * dist P C + dist P B * dist P D) * s3
  -- 17. algebra, from 3
  have s17 : dist P A * dist P D * c * (dist P A * dist P C) = dist P A * dist P D * c * (dist P B * dist P D) := by linear_combination (dist P A * dist P D * c) * s3
  -- 18. algebra, from 3
  have s18 : dist P A * dist P B * c * (dist P A * dist P C) = dist P A * dist P B * c * (dist P B * dist P D) := by linear_combination (dist P A * dist P B * c) * s3
  -- 19. calculation
  have s19 : dist D C ^ 2 * dist P A ^ 2 = dist P D ^ 2 * dist B A ^ 2 := by
    calc dist D C ^ 2 * dist P A ^ 2 = (dist C P ^ 2 + dist P D ^ 2 - 2 * (dist C P * dist P D * c)) * dist P A ^ 2 := by
          simp only [hD1] at s17 ⊢
          linear_combination (dist P A ^ 2) * s13
      _ = (dist P A * dist P C) ^ 2 + dist P A ^ 2 * dist P D ^ 2 - 2 * (dist P A * dist P D * c * (dist P A * dist P C)) := by
          rw [dist_comm P A, dist_comm P D, dist_comm P C]
          exact (by ring1)
      _ = (dist P B * dist P D) ^ 2 + dist P A ^ 2 * dist P D ^ 2 - 2 * (dist P A * dist P D * c * (dist P B * dist P D)) := by linear_combination s16 + (-2) * s17
      _ = dist P D ^ 2 * (dist A P ^ 2 + dist P B ^ 2 - 2 * (dist A P * dist P B * c)) := by
          rw [dist_comm P D, dist_comm P B, dist_comm P A]
          exact (by ring1)
      _ = dist P D ^ 2 * dist B A ^ 2 := by
          simp only [hD1] at s17 ⊢
          linear_combination (-(dist P D ^ 2)) * s9
  -- 20. calculation
  have s20 : dist C B ^ 2 * dist P A ^ 2 = dist P B ^ 2 * dist A D ^ 2 := by
    calc dist C B ^ 2 * dist P A ^ 2 = (dist B P ^ 2 + dist P C ^ 2 + 2 * (dist B P * dist P C * c)) * dist P A ^ 2 := by
          simp only [hD1] at s18 ⊢
          linear_combination (dist P A ^ 2) * s11
      _ = dist P A ^ 2 * dist P B ^ 2 + (dist P A * dist P C) ^ 2 + 2 * (dist P A * dist P B * c * (dist P A * dist P C)) := by
          rw [dist_comm P A, dist_comm P C, dist_comm P B]
          exact (by ring1)
      _ = dist P A ^ 2 * dist P B ^ 2 + (dist P B * dist P D) ^ 2 + 2 * (dist P A * dist P B * c * (dist P B * dist P D)) := by linear_combination s16 + (2) * s18
      _ = dist P B ^ 2 * (dist D P ^ 2 + dist P A ^ 2 + 2 * (dist D P * dist P A * c)) := by
          rw [dist_comm P B, dist_comm P A, dist_comm P D]
          exact (by ring1)
      _ = dist P B ^ 2 * dist A D ^ 2 := by
          simp only [hD1] at s18 ⊢
          linear_combination (-(dist P B ^ 2)) * s15
  -- 21. mun:distance-nonneg P := D, Q := C
  have s21 : dist D C ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := D) (Q := C))
  -- 22. mun:distance-nonneg Q := A
  have s22 : dist P A ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := P) (Q := A))
  -- 23. mun:distance-nonneg Q := D
  have s23 : dist P D ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := P) (Q := D))
  -- 24. mun:distance-nonneg P := B, Q := A
  have s24 : dist B A ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := B) (Q := A))
  -- 25. mun:distance-nonneg P := C, Q := B
  have s25 : dist C B ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := C) (Q := B))
  -- 26. mun:distance-nonneg Q := B
  have s26 : dist P B ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := P) (Q := B))
  -- 27. mun:distance-nonneg P := A, Q := D
  have s27 : dist A D ≥ 0 := by exact (Parley.Items.Stdlib.Geometry.mun_distance_nonneg (P := A) (Q := D))
  -- 28. mun:product-nonneg x := |DC|, y := |PA|, from 21, 22
  have s28 : dist D C * dist P A ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := dist D C) (y := dist P A) s21 s22)
  -- 29. mun:product-nonneg x := |PD|, y := |BA|, from 23, 24
  have s29 : dist P D * dist B A ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := dist P D) (y := dist B A) s23 s24)
  -- 30. mun:product-nonneg x := |CB|, y := |PA|, from 22, 25
  have s30 : dist C B * dist P A ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := dist C B) (y := dist P A) s25 s22)
  -- 31. mun:product-nonneg x := |PB|, y := |AD|, from 26, 27
  have s31 : dist P B * dist A D ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := dist P B) (y := dist A D) s26 s27)
  -- 32. algebra, from 19
  have s32 : (dist D C * dist P A) ^ 2 = (dist P D * dist B A) ^ 2 := by linear_combination s19
  -- 33. mun:square-equal x := |DC|·|PA|, y := |PD|·|BA|, from 28, 29, 32
  have s33 : dist D C * dist P A = dist P D * dist B A := by exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := dist D C * dist P A) (y := dist P D * dist B A) s28 s29)).mp s32
  -- 34. algebra, from 20
  have s34 : (dist C B * dist P A) ^ 2 = (dist P B * dist A D) ^ 2 := by linear_combination s20
  -- 35. mun:square-equal x := |CB|·|PA|, y := |PB|·|AD|, from 30, 31, 34
  have s35 : dist C B * dist P A = dist P B * dist A D := by exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := dist C B * dist P A) (y := dist P B * dist A D) s30 s31)).mp s34
  -- 36. algebra, from 33
  have s36 : dist A B * (dist D C * dist P A) = dist A B * (dist P D * dist B A) := by
    rw [dist_comm D C, dist_comm P A, dist_comm P D, dist_comm B A] at s33
    rw [dist_comm D C, dist_comm P A, dist_comm P D, dist_comm B A]
    exact (by linear_combination (dist A B) * s33)
  -- 37. algebra, from 35
  have s37 : dist A D * (dist C B * dist P A) = dist A D * (dist P B * dist A D) := by linear_combination (dist A D) * s35
  -- 38. algebra, from D1, 9
  have s38 : dist P D * dist B A ^ 2 = dist P D * (dist A P ^ 2 + dist P B ^ 2 - 2 * (dist A P * dist P B * c)) := by
    simp only [hD1] at ⊢
    linear_combination (dist P D) * s9
  -- 39. algebra, from D1, 15
  have s39 : dist P B * dist A D ^ 2 = dist P B * (dist D P ^ 2 + dist P A ^ 2 + 2 * (dist D P * dist P A * c)) := by
    simp only [hD1] at ⊢
    linear_combination (dist P B) * s15
  -- 40. algebra, from 3
  have s40 : (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) = (dist A P + dist P C) * (dist B P + dist P D) * dist P A := by
    rw [dist_comm P A, dist_comm P C, dist_comm P B, dist_comm P D] at s3
    rw [dist_comm P A, dist_comm P B, dist_comm P D, dist_comm P C]
    exact (by linear_combination (-dist B P - dist D P) * s3)
  -- 41. substitute
  have s41 : (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) = dist A C * (dist B P + dist P D) * dist P A := by
    have c1 : dist A P + dist P C = dist A C := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := C) (S := P) hH10)
    have row1 : (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) = dist A C * (dist B P + dist P D) * dist P A := Eq.subst (motive := (fun t : ℝ => (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) = t * (dist B P + dist P D) * dist P A)) c1 s40
    exact row1
  -- 42. substitute
  have s42 : (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) = dist A C * dist B D * dist P A := by
    have c1 : dist B P + dist P D = dist B D := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := B) (Q := D) (S := P) hH11)
    have row1 : (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) = dist A C * dist B D * dist P A := Eq.subst (motive := (fun t : ℝ => (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) = dist A C * t * dist P A)) c1 s41
    exact row1
  -- 43. calculation
  have s43 : (dist A B * dist C D + dist A D * dist B C) * dist P A = dist A C * dist B D * dist P A := by
    calc (dist A B * dist C D + dist A D * dist B C) * dist P A = dist P D * dist B A ^ 2 + dist P B * dist A D ^ 2 := by
          rw [dist_comm D C, dist_comm P A, dist_comm P D, dist_comm B A] at s36
          rw [dist_comm C B, dist_comm P A, dist_comm P B] at s37
          rw [dist_comm P A, dist_comm P D, dist_comm P B, dist_comm B A]
          exact (by linear_combination s36 + s37)
      _ = dist P D * (dist A P ^ 2 + dist P B ^ 2 - 2 * (dist A P * dist P B * c)) + dist P B * (dist D P ^ 2 + dist P A ^ 2 + 2 * (dist D P * dist P A * c)) := by
          rw [dist_comm P D, dist_comm B A, dist_comm P B] at s38
          rw [dist_comm P B, dist_comm P A] at s39
          rw [dist_comm P D, dist_comm P B, dist_comm B A, dist_comm P A]
          exact (by linear_combination s38 + s39)
      _ = (dist P B + dist P D) * (dist P A ^ 2 + dist P B * dist P D) := by
          rw [dist_comm P D, dist_comm P B, dist_comm P A]
          exact (by ring1)
      _ = dist A C * dist B D * dist P A := s42
  -- 44. axi:distance-positive Q := A, from 1
  have s44 : dist P A > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := P) (Q := A) (Ne.symm s1a))
  -- 45. mun:multiply-cancel a := |AC|·|BD|, b := |AB|·|CD| + |AD|·|BC|, c := |PA|, from 43
  have r262_1 : dist P A ≠ 0 := ne_of_gt (by linarith only [s44])
  exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := dist A C * dist B D) (b := dist A B * dist C D + dist A D * dist B C) (c := dist P A) s43.symm r262_1)

end Parley.Proofs.Wiedijk.Ptolemy.CyclicPtolemy
