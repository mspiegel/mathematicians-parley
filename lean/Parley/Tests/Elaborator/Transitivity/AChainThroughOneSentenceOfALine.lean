module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainThroughOneSentenceOfALine

theorem a_chain_through_one_sentence_of_a_line (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : 0 < a ∧ a ≤ b) (hH5 : b < c) :
    a < c := by
  -- 1. transitivity, from H4, H5
  have s1 : a < c := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.Transitivity.AChainThroughOneSentenceOfALine
