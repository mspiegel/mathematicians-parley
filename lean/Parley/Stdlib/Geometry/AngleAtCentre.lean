module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.CircleCentreApart
public import Parley.Stdlib.Geometry.HalfTurn

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AngleAtCentre

theorem angle_at_centre (A : ℂ) (B : ℂ) (C : ℂ) (O : ℂ) (hH5 : A ≠ C) (hH6 : B ≠ C) (hH7 : dist A O = dist B O) (hH8 : dist A O = dist C O) :
    (∃ k : ℤ, Complex.arg ((B - O) / (A - O)) = 2 * Complex.arg ((B - C) / (A - C)) + 2 * (k : ℝ) * Real.pi) := by
  -- 1. mun:circle-centre-apart X := A, Y := C, from H5, H8
  have s1 : A ≠ O := by exact (Parley.Stdlib.Geometry.CircleCentreApart.circle_centre_apart (X := A) (Y := C) (O := O) hH5 hH8)
  -- 2. mun:circle-centre-apart X := C, Y := A, from H5, H8
  have s2 : C ≠ O := by exact (Parley.Stdlib.Geometry.CircleCentreApart.circle_centre_apart (X := C) (Y := A) (O := O) (Ne.symm hH5) hH8.symm)
  -- 3. calculation
  have s3 : dist B O = dist C O := by
    calc dist B O = dist A O := hH7.symm
      _ = dist C O := hH8
  -- 4. mun:circle-centre-apart X := B, Y := C, from H6, 3
  have s4 : B ≠ O := by exact (Parley.Stdlib.Geometry.CircleCentreApart.circle_centre_apart (X := B) (Y := C) (O := O) hH6 s3)
  -- 5. mun:isosceles-signed-angles B := C, Q := O, from H5, H8, 1, 2
  have s5 : Complex.arg ((C - A) / (O - A)) = Complex.arg ((O - C) / (A - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_isosceles_signed_angles (A := A) (B := C) (Q := O) s1 s2 hH5 hH8)
  -- 6. mun:isosceles-signed-angles A := C, Q := O, from H6, 2, 3, 4
  have s6 : Complex.arg ((B - C) / (O - C)) = Complex.arg ((O - B) / (C - B)) := by exact (Parley.Items.Stdlib.Geometry.mun_isosceles_signed_angles (A := C) (B := B) (Q := O) s2 s4 (Ne.symm hH6) s3.symm)
  -- 7. thm:signed-angle-sum P := A, Q := O, R := C, from H5, 1, 2
  have s7 : Complex.arg ((A - O) / (C - O)) + Complex.arg ((O - C) / (A - C)) + Complex.arg ((C - A) / (O - A)) ∈ ({-Real.pi, Real.pi} : Set ℝ) := by exact (Parley.Items.Stdlib.Geometry.thm_signed_angle_sum (P := A) (Q := O) (R := C) s1 (Ne.symm s2) hH5)
  -- 8. thm:signed-angle-sum P := C, Q := O, R := B, from H6, 2, 4
  have s8 : Complex.arg ((C - O) / (B - O)) + Complex.arg ((O - B) / (C - B)) + Complex.arg ((B - C) / (O - C)) ∈ ({-Real.pi, Real.pi} : Set ℝ) := by exact (Parley.Items.Stdlib.Geometry.thm_signed_angle_sum (P := C) (Q := O) (R := B) s2 (Ne.symm s4) (Ne.symm hH6))
  -- 9. obtain i: mun:three-rays Q := O, X := C, from 1, 2, 4
  obtain ⟨i, s9⟩ := (Parley.Items.Stdlib.Geometry.mun_three_rays (A := A) (B := B) (Q := O) (X := C) s1 s4 s2)
  -- 10. obtain j: mun:three-rays Q := C, X := O, from H5, H6, 2
  obtain ⟨j, s10⟩ := (Parley.Items.Stdlib.Geometry.mun_three_rays (A := A) (B := B) (Q := C) (X := O) hH5 hH6 (Ne.symm s2))
  -- 11. obtain m: mun:three-rays B := A, Q := O, X := C, from 1, 2
  obtain ⟨m, s11⟩ := (Parley.Items.Stdlib.Geometry.mun_three_rays (A := A) (B := A) (Q := O) (X := C) s1 s1 s2)
  -- 12. obtain p: mun:three-rays A := C, B := C, Q := O, X := B, from 2, 4
  obtain ⟨p, s12⟩ := (Parley.Items.Stdlib.Geometry.mun_three_rays (A := C) (B := C) (Q := O) (X := B) s2 s2 s4)
  -- 13. mun:signed-angle-zero P := A, Q := O, from 1
  have s13 : Complex.arg ((A - O) / (A - O)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_zero (P := A) (Q := O) s1)
  -- 14. mun:signed-angle-zero P := C, Q := O, from 2
  have s14 : Complex.arg ((C - O) / (C - O)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_signed_angle_zero (P := C) (Q := O) s2)
  -- 15. mun:signed-angle-real P := A, Q := O, R := B, from 1, 4
  -- 16. mun:signed-angle-real P := A, Q := C, R := B, from H5, H6
  -- 17. mun:signed-angle-real P := A, Q := O, R := C, from 1, 2
  -- 18. mun:signed-angle-real P := C, Q := O, R := B, from 2, 4
  -- 19. mun:signed-angle-real P := C, Q := O, R := A, from 1, 2
  -- 20. mun:signed-angle-real P := A, Q := C, R := O, from H5, 2
  -- 21. mun:signed-angle-real P := O, Q := A, R := C, from H5, 1
  -- 22. mun:signed-angle-real P := B, Q := O, R := C, from 2, 4
  -- 23. mun:signed-angle-real P := C, Q := B, R := O, from H6, 4
  -- 24. mun:signed-angle-real P := O, Q := C, R := B, from H6, 2
  -- 25. obtain q: mun:half-turn x := ∡COA + ∡ACO + ∡OAC, from 7
  obtain ⟨q, s25⟩ := (Parley.Stdlib.Geometry.HalfTurn.half_turn (x := Complex.arg ((A - O) / (C - O)) + Complex.arg ((O - C) / (A - C)) + Complex.arg ((C - A) / (O - A))) s7)
  -- 26. obtain r: mun:half-turn x := ∡BOC + ∡CBO + ∡OCB, from 8
  obtain ⟨r, s26⟩ := (Parley.Stdlib.Geometry.HalfTurn.half_turn (x := Complex.arg ((C - O) / (B - O)) + Complex.arg ((O - B) / (C - B)) + Complex.arg ((B - C) / (O - C))) s8)
  -- 27. substitute ∡OAC = ∡ACO (line 5) into line 25
  have s27 : Complex.arg ((A - O) / (C - O)) + Complex.arg ((O - C) / (A - C)) + Complex.arg ((O - C) / (A - C)) = (2 * (q : ℝ) + 1) * Real.pi := Eq.subst (motive := (fun t : ℝ => Complex.arg ((A - O) / (C - O)) + Complex.arg ((O - C) / (A - C)) + t = (2 * (q : ℝ) + 1) * Real.pi)) s5 s25
  -- 28. substitute ∡CBO = ∡OCB (line 6) into line 26
  have s28 : Complex.arg ((C - O) / (B - O)) + Complex.arg ((B - C) / (O - C)) + Complex.arg ((B - C) / (O - C)) = (2 * (r : ℝ) + 1) * Real.pi := Eq.subst (motive := (fun t : ℝ => Complex.arg ((C - O) / (B - O)) + t + Complex.arg ((B - C) / (O - C)) = (2 * (r : ℝ) + 1) * Real.pi)) s6.symm s26
  -- 29. substitute ∡AOA = 0 (line 13) into line 11
  have s29 : Complex.arg ((C - O) / (A - O)) + Complex.arg ((A - O) / (C - O)) = 2 * (m : ℝ) * Real.pi := by (have h := Eq.subst (motive := (fun t : ℝ => Complex.arg ((C - O) / (A - O)) + Complex.arg ((A - O) / (C - O)) = t + 2 * (m : ℝ) * Real.pi)) s13 s11; push_cast [zero_add] at h ⊢; exact_mod_cast h)
  -- 30. substitute ∡COC = 0 (line 14) into line 12
  have s30 : Complex.arg ((B - O) / (C - O)) + Complex.arg ((C - O) / (B - O)) = 2 * (p : ℝ) * Real.pi := by (have h := Eq.subst (motive := (fun t : ℝ => Complex.arg ((B - O) / (C - O)) + Complex.arg ((C - O) / (B - O)) = t + 2 * (p : ℝ) * Real.pi)) s14 s12; push_cast [zero_add] at h ⊢; exact_mod_cast h)
  -- 31. algebra, from 9
  have s31 : Complex.arg ((B - O) / (A - O)) = Complex.arg ((C - O) / (A - O)) + Complex.arg ((B - O) / (C - O)) - 2 * (i : ℝ) * Real.pi := by linear_combination (-1) * s9
  -- 32. substitute
  have s32 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - Complex.arg ((A - O) / (C - O)) + Complex.arg ((B - O) / (C - O)) - 2 * (i : ℝ) * Real.pi := by
    have c1 : Complex.arg ((C - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - Complex.arg ((A - O) / (C - O)) := by linear_combination s29
    have row1 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - Complex.arg ((A - O) / (C - O)) + Complex.arg ((B - O) / (C - O)) - 2 * (i : ℝ) * Real.pi := Eq.subst (motive := (fun t : ℝ => Complex.arg ((B - O) / (A - O)) = t + Complex.arg ((B - O) / (C - O)) - 2 * (i : ℝ) * Real.pi)) c1 s31
    exact row1
  -- 33. substitute
  have s33 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - Complex.arg ((A - O) / (C - O)) + (2 * (p : ℝ) * Real.pi - Complex.arg ((C - O) / (B - O))) - 2 * (i : ℝ) * Real.pi := by
    have c1 : Complex.arg ((B - O) / (C - O)) = 2 * (p : ℝ) * Real.pi - Complex.arg ((C - O) / (B - O)) := by linear_combination s30
    have row1 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - Complex.arg ((A - O) / (C - O)) + (2 * (p : ℝ) * Real.pi - Complex.arg ((C - O) / (B - O))) - 2 * (i : ℝ) * Real.pi := Eq.subst (motive := (fun t : ℝ => Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - Complex.arg ((A - O) / (C - O)) + t - 2 * (i : ℝ) * Real.pi)) c1 s32
    exact row1
  -- 34. substitute
  have s34 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - ((2 * (q : ℝ) + 1) * Real.pi - 2 * Complex.arg ((O - C) / (A - C))) + (2 * (p : ℝ) * Real.pi - Complex.arg ((C - O) / (B - O))) - 2 * (i : ℝ) * Real.pi := by
    have c1 : Complex.arg ((A - O) / (C - O)) = (2 * (q : ℝ) + 1) * Real.pi - 2 * Complex.arg ((O - C) / (A - C)) := by linear_combination s27
    have row1 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - ((2 * (q : ℝ) + 1) * Real.pi - 2 * Complex.arg ((O - C) / (A - C))) + (2 * (p : ℝ) * Real.pi - Complex.arg ((C - O) / (B - O))) - 2 * (i : ℝ) * Real.pi := Eq.subst (motive := (fun t : ℝ => Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - t + (2 * (p : ℝ) * Real.pi - Complex.arg ((C - O) / (B - O))) - 2 * (i : ℝ) * Real.pi)) c1 s33
    exact row1
  -- 35. substitute
  have s35 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - ((2 * (q : ℝ) + 1) * Real.pi - 2 * Complex.arg ((O - C) / (A - C))) + (2 * (p : ℝ) * Real.pi - ((2 * (r : ℝ) + 1) * Real.pi - 2 * Complex.arg ((B - C) / (O - C)))) - 2 * (i : ℝ) * Real.pi := by
    have c1 : Complex.arg ((C - O) / (B - O)) = (2 * (r : ℝ) + 1) * Real.pi - 2 * Complex.arg ((B - C) / (O - C)) := by linear_combination s28
    have row1 : Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - ((2 * (q : ℝ) + 1) * Real.pi - 2 * Complex.arg ((O - C) / (A - C))) + (2 * (p : ℝ) * Real.pi - ((2 * (r : ℝ) + 1) * Real.pi - 2 * Complex.arg ((B - C) / (O - C)))) - 2 * (i : ℝ) * Real.pi := Eq.subst (motive := (fun t : ℝ => Complex.arg ((B - O) / (A - O)) = 2 * (m : ℝ) * Real.pi - ((2 * (q : ℝ) + 1) * Real.pi - 2 * Complex.arg ((O - C) / (A - C))) + (2 * (p : ℝ) * Real.pi - t) - 2 * (i : ℝ) * Real.pi)) c1 s34
    exact row1
  -- 36. algebra, from 35
  have s36 : Complex.arg ((B - O) / (A - O)) = 2 * (Complex.arg ((O - C) / (A - C)) + Complex.arg ((B - C) / (O - C))) + 2 * ((m : ℝ) + (p : ℝ) - (i : ℝ) - (q : ℝ) - (r : ℝ) - 1) * Real.pi := by linear_combination s35
  -- 37. substitute ∡ACO + ∡OCB = ∡ACB + 2·j·π (line 10) into line 36
  have s37 : Complex.arg ((B - O) / (A - O)) = 2 * (Complex.arg ((B - C) / (A - C)) + 2 * (j : ℝ) * Real.pi) + 2 * ((m : ℝ) + (p : ℝ) - (i : ℝ) - (q : ℝ) - (r : ℝ) - 1) * Real.pi := Eq.subst (motive := (fun t : ℝ => Complex.arg ((B - O) / (A - O)) = 2 * t + 2 * ((m : ℝ) + (p : ℝ) - (i : ℝ) - (q : ℝ) - (r : ℝ) - 1) * Real.pi)) s10 s36
  -- 38. algebra, from 37
  have s38 : Complex.arg ((B - O) / (A - O)) = 2 * Complex.arg ((B - C) / (A - C)) + 2 * (2 * (j : ℝ) + (m : ℝ) + (p : ℝ) - (i : ℝ) - (q : ℝ) - (r : ℝ) - 1) * Real.pi := by linear_combination s37
  -- 39. exhibit, from 38
  exact ⟨2 * j + m + p - i - q - r - 1, by exact_mod_cast s38⟩

end Parley.Stdlib.Geometry.AngleAtCentre
