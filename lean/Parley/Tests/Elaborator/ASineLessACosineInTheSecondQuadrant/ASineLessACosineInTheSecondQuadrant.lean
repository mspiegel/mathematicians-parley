module

public import AlgebraTactics
public import ArithTactics
public import InstanceTactics
public import NormTactics
public import RealTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/elaborator/a-sine-less-a-cosine-in-the-second-quadrant.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASineLessACosineInTheSecondQuadrant.ASineLessACosineInTheSecondQuadrant

theorem a_sine_less_a_cosine_in_the_second_quadrant (x : ℝ) (hH2 : Real.pi / 2 ≤ x) (hH3 : x ≤ Real.pi) :
    Real.sin x - Real.cos x ≥ 1 := by
  -- 1. real arithmetic
  have s1 : 0 < Real.pi / 2 := by parley_real
  -- 2. transitivity, from H2, 1
  have s2 : 0 < x := by exact lt_of_lt_of_le s1 hH2
  -- 3. inequalities
  have s3 : 0 ≤ x := by linarith only [s2]
  -- 4. def:interval, from H3, 3
  have s4 : x ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := Real.pi))).mpr ⟨⟨by trivial, s3⟩, hH3⟩
  -- 5. mun:sin-nonneg a := x, from 4
  have s5 : 0 ≤ Real.sin x := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x) s4)
  -- 6. inequalities
  have s6 : 0 ≤ x - Real.pi / 2 := by linarith only [hH2]
  -- 7. real arithmetic
  have s7 : -(Real.pi / 2) ≤ 0 := by parley_real
  -- 8. inequalities, from H3, 7
  have s8 : x - Real.pi / 2 ≤ Real.pi := by linarith only [hH3, s7]
  -- 9. def:interval, from 6, 8
  have s9 : x - Real.pi / 2 ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := x - Real.pi / 2) (a := (0 : ℝ)) (b := Real.pi))).mpr ⟨⟨by trivial, s6⟩, s8⟩
  -- 10. mun:sin-nonneg a := x − π/2, from 9
  have s10 : 0 ≤ Real.sin (x - Real.pi / 2) := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := x - Real.pi / 2) s9)
  -- 11. thm:cos-add a := x − π/2, b := π/2
  have s11 : Real.cos (x - Real.pi / 2 + Real.pi / 2) = Real.cos (x - Real.pi / 2) * Real.cos (Real.pi / 2) - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) := by
    have hI : Real.cos (x - Real.pi / 2 + Real.pi / 2) = Real.cos (x - Real.pi / 2) * Real.cos (Real.pi / 2) - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ) - (Real.pi : ℂ) / 2) (b := (Real.pi : ℂ) / 2)))
    exact hI
  -- 12. algebra
  have s12 : x - Real.pi / 2 + Real.pi / 2 = x := by parley_ring
  -- 13. substitute (x − π/2) + π/2 = x (line 12)
  have s13 : Real.cos (x - Real.pi / 2 + Real.pi / 2) = Real.cos x := by (have h := congrArg (fun t : ℝ => Real.cos t) s12; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 14. real arithmetic
  have s14a : Real.cos (Real.pi / 2) = 0 := by parley_real
  have s14b : Real.sin (Real.pi / 2) = 1 := by parley_real
  -- 15. substitute cos(π/2) = 0 (line 14)
  have s15 : Real.cos (x - Real.pi / 2) * Real.cos (Real.pi / 2) - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) = Real.cos (x - Real.pi / 2) * 0 - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) := by (have h := congrArg (fun t : ℝ => Real.cos (x - Real.pi / 2) * t - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2)) s14a; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 16. substitute sin(π/2) = 1 (line 14)
  have s16 : Real.cos (x - Real.pi / 2) * 0 - Real.sin (x - Real.pi / 2) * Real.sin (Real.pi / 2) = Real.cos (x - Real.pi / 2) * 0 - Real.sin (x - Real.pi / 2) * 1 := by (have h := congrArg (fun t : ℝ => Real.cos (x - Real.pi / 2) * 0 - Real.sin (x - Real.pi / 2) * t) s14b; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 17. algebra, from 11, 13, 15, 16
  have s17 : Real.cos x = -Real.sin (x - Real.pi / 2) := by linear_combination (norm := parley_norm) s11 + (-1) * s13 + s15 + s16
  -- 18. algebra, from 17
  have s18 : Real.sin (x - Real.pi / 2) = -Real.cos x := by linear_combination (norm := parley_norm) s17
  -- 19. transitivity, from 10, 18
  have s19 : 0 ≤ -Real.cos x := by exact LE.le.trans_eq s10 s18
  -- 20. inequalities, from 5, 19
  have s20 : 0 ≤ Real.sin x - Real.cos x := by linarith only [s5, s19]
  -- 21. mun:product-nonneg x := sin(x), y := sin(x − π/2), from 5, 10
  have s21 : Real.sin x * Real.sin (x - Real.pi / 2) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sin x) (y := Real.sin (x - Real.pi / 2)) s5 s10)
  -- 22. mun:sin-cos-squares a := x
  have s22 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
    have hI : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))))
    exact hI
  -- 23. algebra, from 17, 22
  have s23 : 1 + 2 * Real.sin x * Real.sin (x - Real.pi / 2) = (Real.sin x - Real.cos x) ^ 2 := by linear_combination (norm := parley_norm) (2 * Real.sin x) * s17 + (-1) * s22
  -- 24. inequalities
  have s24 : 1 ^ 2 ≤ 1 + 2 * Real.sin x * Real.sin (x - Real.pi / 2) := by linarith only [s21]
  -- 25. transitivity, from 23, 24
  have s25 : 1 ^ 2 ≤ (Real.sin x - Real.cos x) ^ 2 := by exact LE.le.trans_eq s24 s23.symm.symm
  -- 26. mun:square-le x := 1, y := sin(x) − cos(x), from 20, 25
  have r104_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have s26 : 1 ≤ Real.sin x - Real.cos x := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (1 : ℝ)) (y := Real.sin x - Real.cos x) (by norm_num) s20)).mpr s25
  exact s26

end Parley.Tests.Elaborator.ASineLessACosineInTheSecondQuadrant.ASineLessACosineInTheSecondQuadrant
