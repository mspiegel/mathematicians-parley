module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-calculation-asks-no-membership.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACalculationAsksNoMembership.ACalculationAsksNoMembership

theorem a_calculation_asks_no_membership (k : ℤ) (hH1 : 0 < k) (y : ℝ) (hH3 : y ≤ 2 * (LeanBridges.Counting.factorial k : ℝ)) (hH4 : 2 * (LeanBridges.Counting.factorial k : ℤ) < 2 * (LeanBridges.Counting.factorial k : ℤ) * 2) :
    y < 2 * (LeanBridges.Counting.factorial k : ℝ) * 2 := by
  -- 1. calculation
  calc y ≤ 2 * (LeanBridges.Counting.factorial k : ℝ) := hH3
    _ < 2 * (LeanBridges.Counting.factorial k : ℝ) * 2 := by exact_mod_cast hH4

end Parley.Tests.Elaborator.ACalculationAsksNoMembership.ACalculationAsksNoMembership
