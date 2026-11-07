module

public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineASubstituteIsPutInto

theorem a_for_all_line_a_substitute_is_put_into (b : ℝ) (hH2 : ∀ x : ℝ, x ^ 2 ≥ 0) :
    (∀ y : ℝ, y = b → b ^ 2 ≥ 0) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y = b → b ^ 2 ≥ 0 := by
    intro y
    intro hA1
    -- 1.1. substitute y = b (A1) into H2
    have s1_1 : b ^ 2 ≥ 0 := by
      have at0 := (hH2 b)
      parley_subst_at hA1 at0
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineASubstituteIsPutInto
