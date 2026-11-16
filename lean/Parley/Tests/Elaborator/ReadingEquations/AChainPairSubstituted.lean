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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AChainPairSubstituted

theorem a_chain_pair_substituted (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = b ∧ b = c) :
    a + 1 = c + 1 := by
  -- 1. substitute a = c (H4)
  exact congrArg (fun t : ℝ => t + 1) (Eq.trans (hH4.1) hH4.2)

end Parley.Tests.Elaborator.ReadingEquations.AChainPairSubstituted
