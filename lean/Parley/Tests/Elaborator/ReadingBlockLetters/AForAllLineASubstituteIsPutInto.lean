module

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
  intro y
  intro hA1
  -- 1.1. substitute y = b (A1) into H2
  (have h := Eq.subst (motive := (fun t : ℝ => t ^ 2 ≥ 0)) hA1 (hH2 y); push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineASubstituteIsPutInto
