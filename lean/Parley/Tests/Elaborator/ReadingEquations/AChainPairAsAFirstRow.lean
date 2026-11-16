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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AChainPairAsAFirstRow

theorem a_chain_pair_as_a_first_row (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = b ∧ b = c) :
    a ≤ c := by
  -- 1. inequalities
  linarith only [Eq.trans (hH4.1) hH4.2]

end Parley.Tests.Elaborator.ReadingEquations.AChainPairAsAFirstRow
