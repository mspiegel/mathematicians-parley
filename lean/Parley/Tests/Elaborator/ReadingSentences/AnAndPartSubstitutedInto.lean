module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartSubstitutedInto

theorem an_and_part_substituted_into (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ a < b) (hH4 : b = 2) :
    a < 2 := by
  -- 1. substitute b = 2 (H4) into H3
  (have h := Eq.subst (motive := (fun t : ℝ => a < t)) hH4 hH3.2; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartSubstitutedInto
