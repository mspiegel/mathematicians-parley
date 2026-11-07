module

public import Tactics
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.RealPowersAdded

theorem real_powers_added (x : ℝ) (hH2 : x ≠ 0) (a : ℝ) (b : ℝ) :
    (x : ℂ) ^ ((a : ℂ) + (b : ℂ)) = (x : ℂ) ^ (a : ℂ) * (x : ℂ) ^ (b : ℂ) := by
  -- 1. mun:real-power-sum, from H2
  have s1 : (x : ℂ) ^ ((a : ℂ) + (b : ℂ)) = (x : ℂ) ^ (a : ℂ) * (x : ℂ) ^ (b : ℂ) := by exact (Parley.Items.Stdlib.Numbers.mun_real_power_sum (x := (x : ℂ)) (by parley_side) (a := (a : ℂ)) (b := (b : ℂ)))
  all_goals exact s1

end Parley.Tests.Notations.Powers.RealPowersAdded
