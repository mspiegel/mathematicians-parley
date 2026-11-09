module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsTheSubstitutedEquation

theorem an_and_part_as_the_substituted_equation (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    a + b = a + 2 := by
  -- 1. substitute b = 2 (H3)
  (have h := congrArg (fun t : ℝ => a + t) hH3.2; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsTheSubstitutedEquation
