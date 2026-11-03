module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainOfEquations

theorem a_chain_of_equations {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A = B) (hH5 : B = C) :
    A = C := by
  -- 1. transitivity, from H4, H5
  have s1 : A = C := by parley_set_side
  all_goals exact s1

end Parley.Tests.Elaborator.Transitivity.AChainOfEquations
