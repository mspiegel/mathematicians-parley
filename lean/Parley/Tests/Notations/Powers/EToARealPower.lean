module

public import ComplexTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.EToARealPower

theorem e_to_a_real_power (y : ℝ) :
    Real.exp 1 ^ y = Real.exp y := by
  -- 1. mun:e-power
  (have h := (Parley.Items.Stdlib.Logarithms.mun_e_power (y := (y : ℂ))); parley_of_complex h)

end Parley.Tests.Notations.Powers.EToARealPower
