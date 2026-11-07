module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerAtLeastOne

theorem power_at_least_one (b : ℝ) (m : ℤ) (hH2 : 0 ≤ m) (hH3 : 1 ≤ b) :
    1 ≤ b ^ m.toNat := by
  -- 1. mun:numbers-power-at-least-one a := b, n := m, from H3
  have s1 : 1 ≤ b ^ m.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerAtLeastOne
