module

public import PowerTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SinNegative

theorem sin_negative (a : ℂ) :
    Complex.sin (-a) = -Complex.sin a := by
  -- 1. mun:trigonometry-sin-negative
  have s1 : Complex.sin (-a) = -Complex.sin a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.SinNegative
