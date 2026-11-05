module

public import AlgebraTactics
public import ArithTactics
public import ComplexTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/elaborator/a-sine-less-a-cosine-in-the-second-quadrant.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASineLessACosineInTheSecondQuadrant.ASineLessACosineInTheSecondQuadrant

set_option maxHeartbeats 400000 in
theorem a_sine_less_a_cosine_in_the_second_quadrant (x : ℝ) (hH2 : Real.pi / 2 ≤ x) (hH3 : x ≤ Real.pi) :
    Real.sin x - Real.cos x ≥ 1 := by
  -- 1. real arithmetic
  have s1 : 0 < Real.pi / 2 := by parley_real
  -- 2. transitivity, from H2, 1
  have s2 : 0 < x := by parley_order
  -- 3. inequalities
  have s3 : 0 ≤ x := by parley_order
  -- 4. def:interval, from H3, 3
  have s4 : x ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := Real.pi))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := Real.pi))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:sin-nonneg a := x, from 4
  have s5 : 0 ≤ Real.sin x := by first | linarith [(Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x) s4)] | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x) s4); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x) s4) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x) s4); parley_set_side)
  -- 6. inequalities
  have s6 : 0 ≤ x - Real.pi / 2 := by parley_order
  -- 7. real arithmetic
  have s7 : -(Real.pi / 2) ≤ 0 := by parley_real
  -- 8. inequalities, from H3, 7
  have s8 : x - Real.pi / 2 ≤ Real.pi := by parley_order
  -- 9. def:interval, from 6, 8
  have s9 : x - Real.pi / 2 ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := x - Real.pi / 2) (a := (0 : ℝ)) (b := Real.pi))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := x - Real.pi / 2) (a := (0 : ℝ)) (b := Real.pi))).mpr (by parley_set_side); parley_set_side)
  -- 10. mun:sin-nonneg a := x − π/2, from 9
  have s10 : 0 ≤ Real.sin (x - Real.pi / 2) := by first | linarith [(Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x - Real.pi / 2) s9)] | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x - Real.pi / 2) s9); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x - Real.pi / 2) s9) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x - Real.pi / 2) s9); parley_set_side)
  -- 11. thm:cos-add a := x − π/2, b := π/2
  have s11 : Real.cos (x - Real.pi / 2 + Real.pi / 2) = Real.cos (x - Real.pi / 2) * Real.cos (Real.pi / 2) - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)); parley_set_side)
  -- 12. algebra
  have s12 : x - Real.pi / 2 + Real.pi / 2 = x := by parley_ring
  -- 13. substitute (x − π/2) + π/2 = x (line 12)
  have s13 : Real.cos (x - Real.pi / 2 + Real.pi / 2) = Real.cos x := by parley_subst s12
  -- 14. real arithmetic
  have s14a : Real.cos (Real.pi / 2) = 0 := by parley_real
  have s14b : Real.sin (Real.pi / 2) = 1 := by parley_real
  -- 15. substitute cos(π/2) = 0 (line 14)
  have s15 : Real.cos (x - Real.pi / 2) * Real.cos (Real.pi / 2) - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) = Real.cos (x - Real.pi / 2) * 0 - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) := by parley_subst s14a
  -- 16. substitute sin(π/2) = 1 (line 14)
  have s16 : Real.cos (x - Real.pi / 2) * 0 - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) = Real.cos (x - Real.pi / 2) * 0 - Real.sin (x - Real.pi / 2) * 1 := by parley_subst s14b
  -- 17. algebra, from 11, 13, 15, 16
  have s17 : Real.cos x = -Real.sin (x - Real.pi / 2) := by linear_combination (norm := parley_norm) s11 + (-1) * s13 + s15 + s16
  -- 18. algebra, from 17
  have s18 : Real.sin (x - Real.pi / 2) = -Real.cos x := by linear_combination (norm := parley_norm) s17
  -- 19. transitivity, from 10, 18
  have s19 : 0 ≤ -Real.cos x := by parley_order
  -- 20. inequalities, from 5, 19
  have s20 : 0 ≤ Real.sin x - Real.cos x := by parley_order
  -- 21. mun:product-nonneg x := sin(x), y := sin(x − π/2), from 5, 10
  have s21 : Real.sin x * Real.sin (x - Real.pi / 2) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sin x) (y := Real.sin (x - Real.pi / 2)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sin x) (y := Real.sin (x - Real.pi / 2)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sin x) (y := Real.sin (x - Real.pi / 2)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sin x) (y := Real.sin (x - Real.pi / 2)) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 22. mun:sin-cos-squares a := x
  have s22 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_set_side)
  -- 23. algebra, from 17, 22
  have s23 : 1 + 2 * Real.sin x * Real.sin (x - Real.pi / 2) = (Real.sin x - Real.cos x) ^ 2 := by linear_combination (norm := parley_norm) (2 * Real.sin x) * s17 + (-1) * s22
  -- 24. inequalities
  have s24 : 1 ^ 2 ≤ 1 + 2 * Real.sin x * Real.sin (x - Real.pi / 2) := by parley_order
  -- 25. transitivity, from 23, 24
  have s25 : 1 ^ 2 ≤ (Real.sin x - Real.cos x) ^ 2 := by parley_order
  -- 26. mun:square-le x := 1, y := sin(x) − cos(x), from 20, 25
  have r104_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have s26 : 1 ≤ Real.sin x - Real.cos x := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (1 : ℝ)) (y := Real.sin x - Real.cos x) (by parley_set_side) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (1 : ℝ)) (y := Real.sin x - Real.cos x) (by parley_set_side) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
  all_goals parley_set_side

end Parley.Tests.Elaborator.ASineLessACosineInTheSecondQuadrant.ASineLessACosineInTheSecondQuadrant
