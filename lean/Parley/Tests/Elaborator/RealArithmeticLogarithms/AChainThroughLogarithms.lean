module

public import RealTactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.AChainThroughLogarithms

theorem a_chain_through_logarithms :
    Real.log (4 : ℝ) + Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) := by
  -- 1. calculation
  calc Real.log (4 : ℝ) + Real.log (2 : ℝ) = 2 * Real.log (2 : ℝ) + Real.log (2 : ℝ) := by parley_real
    _ = 3 * Real.log (2 : ℝ) := by parley_real

end Parley.Tests.Elaborator.RealArithmeticLogarithms.AChainThroughLogarithms
