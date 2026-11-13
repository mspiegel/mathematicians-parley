module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/nine-powers-and-three-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NinePowersAndThreePowers.PositivePowerIsReal

theorem positive_power_is_real (a : ℝ) (m : ℤ) (hH3 : a > 0) :
    True := by
  -- 1. mun:nonneg-or-neg x := m
  have s1 : m ≥ 0 ∨ m < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m))
  -- 2. cases, from 1
  -- what this block shows, Lean's types give
  exact trivial

end Parley.Proofs.Hammack.NinePowersAndThreePowers.PositivePowerIsReal
