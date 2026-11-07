module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.ArctanValues

theorem arctan_values :
    Real.arctan (0 : ℝ) = 0 ∧ Real.arctan (1 : ℝ) = Real.pi / 4 := by
  -- 1. mun:trigonometry-arctan-values
  have s1a : Real.arctan (0 : ℝ) = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1 | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1 | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1).symm | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; parley_int_power h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; parley_side)
  have s1b : Real.arctan (1 : ℝ) = Real.pi / 4 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2 | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2 | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2).symm | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; parley_side)
  exact ⟨by parley_side, by parley_side⟩

end Parley.Tests.Stdlib.Trigonometry.ArctanValues
