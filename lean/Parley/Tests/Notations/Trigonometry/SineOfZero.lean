module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.SineOfZero

theorem sine_of_zero :
    Real.sin (0 : ℝ) = 0 := by
  -- 1. mun:sin-zero
  have s1 : Real.sin (0 : ℝ) = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Trigonometry.mun_sin_zero | (have h := Parley.Items.Stdlib.Trigonometry.mun_sin_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_sin_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Trigonometry.mun_sin_zero | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_zero).symm | (have h := Parley.Items.Stdlib.Trigonometry.mun_sin_zero; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_sin_zero; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_sin_zero; parley_int_power h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_sin_zero; parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Trigonometry.SineOfZero
