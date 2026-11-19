module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Stdlib.Geometry.AngleAtCentre

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.SameArcAngles

theorem same_arc_angles (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (O : ℂ) (hH6 : dist A O = dist B O) (hH7 : dist A O = dist C O) (hH8 : dist A O = dist D O) (hH9 : 0 < Complex.im ((C - A) / (B - A)) * Complex.im ((D - A) / (B - A))) :
    EuclideanGeometry.angle A C B = EuclideanGeometry.angle A D B := by
  -- 1. mun:same-side-off-line P := C, Q := D, from H9
  have s1a : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_1 (A := A) (B := B) (P := C) (Q := D) hH9)
  have s1b : ¬ C ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := A) (B := B) (P := C) (Q := D) hH9)
  -- 2. mun:same-side-off-line P := C, Q := D, from H9
  have s2 : ¬ D ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := A) (B := B) (P := C) (Q := D) hH9)
  -- 3. mun:off-line-apart P := C, from 1
  have s3 : C ≠ A := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := A) (B := B) (P := C) s1a s1b)
  -- 4. mun:off-line-apart P := C, from 1
  have s4 : C ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := A) (B := B) (P := C) s1a s1b)
  -- 5. mun:off-line-apart P := D, from 1, 2
  have s5 : D ≠ A := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := A) (B := B) (P := D) s1a s2)
  -- 6. mun:off-line-apart P := D, from 1, 2
  have s6 : D ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := A) (B := B) (P := D) s1a s2)
  -- 7. obtain i: thm:angle-at-centre, from H6, H7, 3, 4
  obtain ⟨i, s7⟩ := (Parley.Stdlib.Geometry.AngleAtCentre.angle_at_centre (A := A) (B := B) (C := C) (O := O) (Ne.symm s3) (Ne.symm s4) hH6 hH7)
  -- 8. obtain j: thm:angle-at-centre C := D, from H6, H8, 5, 6
  obtain ⟨j, s8⟩ := (Parley.Stdlib.Geometry.AngleAtCentre.angle_at_centre (A := A) (B := B) (C := D) (O := O) (Ne.symm s5) (Ne.symm s6) hH6 hH8)
  -- 9. mun:signed-angle-real P := A, Q := C, R := B, from 3, 4
  -- 10. mun:signed-angle-real P := A, Q := C, R := B, from 3, 4
  have s10 : -Real.pi < Complex.arg ((B - C) / (A - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_real_2 (P := A) (Q := C) (R := B) (Ne.symm s3) (Ne.symm s4))
  -- 11. mun:signed-angle-real P := A, Q := C, R := B, from 3, 4
  have s11 : Complex.arg ((B - C) / (A - C)) ≤ Real.pi := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_real_3 (P := A) (Q := C) (R := B) (Ne.symm s3) (Ne.symm s4))
  -- 12. mun:signed-angle-real P := A, Q := D, R := B, from 5, 6
  -- 13. mun:signed-angle-real P := A, Q := D, R := B, from 5, 6
  have s13 : -Real.pi < Complex.arg ((B - D) / (A - D)) := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_real_2 (P := A) (Q := D) (R := B) (Ne.symm s5) (Ne.symm s6))
  -- 14. mun:signed-angle-real P := A, Q := D, R := B, from 5, 6
  have s14 : Complex.arg ((B - D) / (A - D)) ≤ Real.pi := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_real_3 (P := A) (Q := D) (R := B) (Ne.symm s5) (Ne.symm s6))
  -- 15. calculation
  have s15 : 2 * Complex.arg ((B - C) / (A - C)) + 2 * (i : ℝ) * Real.pi = 2 * Complex.arg ((B - D) / (A - D)) + 2 * (j : ℝ) * Real.pi := by
    calc 2 * Complex.arg ((B - C) / (A - C)) + 2 * (i : ℝ) * Real.pi = Complex.arg ((B - O) / (A - O)) := s7.symm
      _ = 2 * Complex.arg ((B - D) / (A - D)) + 2 * (j : ℝ) * Real.pi := s8
  -- 16. algebra, from 15
  have s16 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) = ((j : ℝ) - (i : ℝ)) * Real.pi := by linear_combination ((1 / 2 : ℝ)) * s15
  -- 17. mun:same-side-turns-alike, from H9
  have s17 : Complex.arg ((B - C) / (A - C)) * Complex.arg ((B - D) / (A - D)) > 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_turns_alike (A := A) (B := B) (C := C) (D := D) hH9)
  -- 18. mun:nonneg-or-neg x := ∡ACB, from 9
  have s18 : Complex.arg ((B - C) / (A - C)) ≥ 0 ∨ Complex.arg ((B - C) / (A - C)) < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := Complex.arg ((B - C) / (A - C))))
  -- 19. cases, from 18
  have s19 : -Real.pi < Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) ∧ Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) < Real.pi := by
    rcases s18 with hC1 | hC2
    · skip
      -- 19.1. mun:factor-positive a := ∡ACB, b := ∡ADB, from C1, 9, 12, 17
      have s19_1 : Complex.arg ((B - D) / (A - D)) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := Complex.arg ((B - C) / (A - C))) (b := Complex.arg ((B - D) / (A - D))) hC1 s17)
      -- 19.2. inequalities
      have s19_2 : Complex.arg ((B - D) / (A - D)) * Complex.arg ((B - C) / (A - C)) > 0 := by linarith only [s17]
      -- 19.3. mun:factor-positive a := ∡ADB, b := ∡ACB, from 9, 19.2
      have r4959_2 : Complex.arg ((B - D) / (A - D)) ≥ 0 := by linarith only [s19_1]
      have s19_3 : Complex.arg ((B - C) / (A - C)) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := Complex.arg ((B - D) / (A - D))) (b := Complex.arg ((B - C) / (A - C))) r4959_2 s19_2)
      -- 19.4. inequalities
      have s19_4 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) > -Complex.arg ((B - D) / (A - D)) := by linarith only [s19_3]
      -- 19.5. inequalities
      have s19_5 : -Complex.arg ((B - D) / (A - D)) ≥ -Real.pi := by linarith only [s14]
      -- 19.6. transitivity, from 19.5, 19.4
      have s19_6 : -Real.pi < Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) := by exact lt_of_le_of_lt s19_5 s19_4
      -- 19.7. inequalities
      have s19_7 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) < Complex.arg ((B - C) / (A - C)) := by linarith only [s19_1]
      -- 19.8. transitivity, from 19.7, 11
      have s19_8 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) < Real.pi := by exact lt_of_lt_of_le s19_7 s11
      -- 19.9. join 19.6, 19.8
      have s19_9 : -Real.pi < Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) ∧ Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) < Real.pi := ⟨s19_6, s19_8⟩
      exact ⟨(s19_9).1, (s19_9).2⟩
    · skip
      -- 19.10. inequalities
      have s19_10 : -Complex.arg ((B - C) / (A - C)) ≥ 0 := by linarith only [hC2]
      -- 19.11. inequalities
      have s19_11 : -Complex.arg ((B - C) / (A - C)) * -Complex.arg ((B - D) / (A - D)) > 0 := by linarith only [s17]
      -- 19.12. mun:factor-positive a := −∡ACB, b := −∡ADB, from 19.10, 19.11
      have s19_12 : -Complex.arg ((B - D) / (A - D)) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := -Complex.arg ((B - C) / (A - C))) (b := -Complex.arg ((B - D) / (A - D))) s19_10 s19_11)
      -- 19.13. inequalities
      have s19_13 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) > Complex.arg ((B - C) / (A - C)) := by linarith only [s19_12]
      -- 19.14. transitivity, from 10, 19.13
      have s19_14 : -Real.pi < Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) := by exact lt_trans s10 s19_13
      -- 19.15. inequalities
      have s19_15 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) < -Complex.arg ((B - D) / (A - D)) := by linarith only [hC2]
      -- 19.16. inequalities
      have s19_16 : -Complex.arg ((B - D) / (A - D)) < Real.pi := by linarith only [s13]
      -- 19.17. transitivity, from 19.15, 19.16
      have s19_17 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) < Real.pi := by exact lt_trans s19_15 s19_16
      -- 19.18. join 19.14, 19.17
      have s19_18 : -Real.pi < Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) ∧ Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) < Real.pi := ⟨s19_14, s19_17⟩
      exact ⟨(s19_18).1, (s19_18).2⟩
  -- 20. substitute ∡ACB − ∡ADB = (j − i)·π (line 16) into line 19
  have s20 : -Real.pi < ((j : ℝ) - (i : ℝ)) * Real.pi := Eq.subst (motive := (fun t : ℝ => -Real.pi < t)) s16 s19.1
  -- 21. substitute ∡ACB − ∡ADB = (j − i)·π (line 16) into line 19
  have s21 : ((j : ℝ) - (i : ℝ)) * Real.pi < Real.pi := Eq.subst (motive := (fun t : ℝ => t < Real.pi)) s16 s19.2
  -- 22. mun:pi-positive
  have s22 : Real.pi > 0 := by exact Parley.Items.Stdlib.Trigonometry.mun_pi_positive
  -- 23. inequalities
  have s23 : Real.pi * -1 < Real.pi * ((j : ℝ) - (i : ℝ)) := by linarith only [s20]
  -- 24. mun:less-scaled x := −1, y := j − i, c := π, from 22, 23
  have s24 : -1 < j - i := by
    have hI : -1 < j - i := by exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (-1 : ℝ)) (y := (j : ℝ) - (i : ℝ)) (c := Real.pi) s22)).mpr s23)
    exact hI
  -- 25. inequalities
  have s25 : Real.pi * ((j : ℝ) - (i : ℝ)) < Real.pi * 1 := by linarith only [s21]
  -- 26. mun:less-scaled x := j − i, y := 1, c := π, from 22, 25
  have s26 : j - i < 1 := by
    have hI : j - i < 1 := by exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (j : ℝ) - (i : ℝ)) (y := (1 : ℝ)) (c := Real.pi) s22)).mpr s25)
    exact hI
  -- 27. mun:integer-step m := −1, n := j − i, from 24
  have s27 : -1 + 1 ≤ j - i := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (-1 : ℤ)) (n := j - i) s24)
  -- 28. inequalities
  have s28 : 0 ≤ j - i := by linarith only [s27]
  -- 29. mun:integer-step m := j − i, n := 1, from 26
  have s29 : j - i + 1 ≤ 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := j - i) (n := (1 : ℤ)) s26)
  -- 30. inequalities
  have s30 : j - i ≤ 0 := by linarith only [s29]
  -- 31. antisymmetry, from 28, 30
  have s31 : j - i = 0 := le_antisymm s30 s28
  -- 32. substitute j − i = 0 (line 31) into line 16
  have s32 : Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) = 0 * Real.pi := by
    have e_w : (j : ℝ) - (i : ℝ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s31; push_cast at h; linear_combination h
    exact Eq.subst (motive := (fun t : ℝ => Complex.arg ((B - C) / (A - C)) - Complex.arg ((B - D) / (A - D)) = t * Real.pi)) e_w s16
  -- 33. algebra, from 32
  have s33 : Complex.arg ((B - C) / (A - C)) = Complex.arg ((B - D) / (A - D)) := by linear_combination s32
  -- 34. calculation
  have r5106_1 : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_1 (A := A) (B := B) (P := C) (Q := D) hH9)
  calc EuclideanGeometry.angle A C B = abs (Complex.arg ((B - C) / (A - C))) := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_size (P := A) (Q := C) (R := B) (Ne.symm s3) (Ne.symm s4) r5106_1).symm
    _ = abs (Complex.arg ((B - D) / (A - D))) := congrArg (fun t : ℝ => abs t) s33
    _ = EuclideanGeometry.angle A D B := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_size (P := A) (Q := D) (R := B) (Ne.symm s5) (Ne.symm s6) r5106_1)

end Parley.Stdlib.Geometry.SameArcAngles
