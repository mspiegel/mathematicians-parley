module

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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AChainPairInACalculationLink

theorem a_chain_pair_in_a_calculation_link (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH5 : a = b ∧ b = c) (hH6 : c = d) :
    a = d := by
  -- 1. calculation
  calc a = c := Eq.trans (hH5.1) hH5.2
    _ = d := hH6

end Parley.Tests.Elaborator.ReadingEquations.AChainPairInACalculationLink
