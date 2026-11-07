module

public import ComplexTactics
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.EToARealPower

theorem e_to_a_real_power (y : ℝ) :
    Real.exp 1 ^ y = Real.exp y := by
  -- 1. mun:e-power
  have s1 : Real.exp 1 ^ y = Real.exp y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))) | (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Powers.EToARealPower
