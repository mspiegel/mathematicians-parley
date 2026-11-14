module

public import Counting
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-calculation-asks-no-membership.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACalculationAsksNoMembership.ACalculationAsksNoMembership

theorem a_calculation_asks_no_membership (k : ℤ) (hH1 : 0 < k) (y : ℝ) (hH3 : y ≤ 2 * (LeanBridges.Counting.factorial k : ℝ)) (hH4 : 2 * (LeanBridges.Counting.factorial k : ℤ) < 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) :
    y < 2 * (LeanBridges.Counting.factorial k : ℝ) * 2 := by
  -- 1. calculation
  calc y ≤ 2 * (LeanBridges.Counting.factorial k : ℝ) := hH3
    _ < 2 * (LeanBridges.Counting.factorial k : ℝ) * 2 := by exact_mod_cast hH4

end Parley.Tests.Elaborator.ACalculationAsksNoMembership.ACalculationAsksNoMembership
