module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.RealPowersAdded

theorem real_powers_added (x : ℝ) (hH2 : x ≠ 0) (a : ℝ) (b : ℝ) :
    (x : ℂ) ^ ((a : ℂ) + (b : ℂ)) = (x : ℂ) ^ (a : ℂ) * (x : ℂ) ^ (b : ℂ) := by
  -- 1. mun:real-power-sum, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_real_power_sum (x := (x : ℂ)) (by exact_mod_cast hH2) (a := (a : ℂ)) (b := (b : ℂ)))

end Parley.Tests.Notations.Powers.RealPowersAdded
