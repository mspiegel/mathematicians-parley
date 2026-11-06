module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/powers-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PowersSaidOnce.APowerWhoseBaseHoldsAFactorial

theorem a_power_whose_base_holds_a_factorial (b : ℤ) (hH1 : 0 ≤ b) (x : ℝ) (z : ℂ) :
    (x : ℂ) * (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b.toNat = (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b.toNat * (x : ℂ) := by
  -- 1. algebra
  have s1 : (x : ℂ) * (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b.toNat = (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b.toNat * (x : ℂ) := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.PowersSaidOnce.APowerWhoseBaseHoldsAFactorial
