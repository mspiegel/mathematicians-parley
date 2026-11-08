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

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineGivingASubstituteItsEquation

theorem a_for_all_line_giving_a_substitute_its_equation (hH1 : ∀ x : ℝ, x ^ 2 = x * x) :
    (∀ y : ℝ, y ^ 2 + 1 = y * y + 1) := by
  -- 1. proof
  intro y
  -- 1.1. substitute y² = y·y (H1)
  parley_subst hH1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineGivingASubstituteItsEquation
