module

public import AlgebraTactics
public import ArithTactics
public import ComplexTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/sine-is-bounded.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SineIsBounded.SineIsBounded

set_option maxHeartbeats 400000 in
theorem sine_is_bounded (x : ℝ) :
    (-1 ≤ Real.sin x ∧ Real.sin x ≤ 1) := by
  -- 1. mun:sin-cos-squares a := x
  have s1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_side)
  -- 2. mun:square-nonneg x := cos(x)
  have s2 : Real.cos x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := Real.cos x))
  -- 3. inequalities
  have s3 : -(Real.cos x ^ 2) ≤ 0 := by parley_order
  -- 4. inequalities
  have s4 : Real.sin x ^ 2 + Real.cos x ^ 2 ≤ 1 := by parley_order
  -- 5. inequalities, from 3, 4
  have s5 : Real.sin x ^ 2 ≤ 1 := by parley_order
  -- 6. contradiction
  have s6 : Real.sin x ≤ 1 := by
    by_contra hS1
    -- 6.1. inequalities, from S1
    have s6_1 : Real.sin x > 1 := by parley_order
    -- 6.2. inequalities, from 6.1
    have s6_2 : Real.sin x > 0 := by parley_order
    -- 6.3. mun:square-less x := 1, y := sin(x), from 6.1
    have r40_1 : (1 : ℤ) ≥ 0 := by parley_arith
    have r40_2 : Real.sin x ≥ 0 := by parley_side
    have s6_3 : 1 ^ 2 < Real.sin x ^ 2 := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (1 : ℝ)) (y := Real.sin x) (by parley_side) (by parley_side))).mp s6_1
    -- 6.4. inequalities, from 6.3
    have s6_4 : ¬ Real.sin x ^ 2 ≤ 1 := by parley_side
    exact s6_4 s5
  -- 7. contradiction
  have s7 : -1 ≤ Real.sin x := by
    by_contra hS2
    -- 7.1. inequalities, from S2
    have s7_1 : Real.sin x < -1 := by parley_order
    -- 7.2. inequalities
    have s7_2 : -Real.sin x > 1 := by parley_order
    -- 7.3. inequalities, from 7.2
    have s7_3 : -Real.sin x > 0 := by parley_order
    -- 7.4. mun:square-less x := 1, y := −sin(x), from 7.2
    have r63_1 : (1 : ℤ) ≥ 0 := by parley_arith
    have r63_2 : -Real.sin x ≥ 0 := by parley_side
    have s7_4 : 1 ^ 2 < (-Real.sin x) ^ 2 := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (1 : ℝ)) (y := -Real.sin x) (by parley_side) (by parley_side))).mp s7_2
    -- 7.5. algebra
    have s7_5 : (-Real.sin x) ^ 2 = Real.sin x ^ 2 := by parley_ring
    -- 7.6. transitivity, from 7.4, 7.5
    have s7_6 : 1 ^ 2 < Real.sin x ^ 2 := by parley_order
    -- 7.7. inequalities, from 7.6
    have s7_7 : ¬ Real.sin x ^ 2 ≤ 1 := by parley_side
    exact s7_7 s5
  -- 8. join 6, 7
  have s8 : -1 ≤ Real.sin x ∧ Real.sin x ≤ 1 := by parley_side
  exact ⟨(s8).1, (s8).2⟩

end Parley.Proofs.Identities.SineIsBounded.SineIsBounded
