module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/an-assume-line-of-several-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnOpeningAssumeOfSeveralSentences

theorem an_opening_assume_of_several_sentences (a : ℝ) (b : ℝ) :
    (a = 1 ∧ b = 2 → a + b = 3) := by
  -- 1. proof
  intro hK1
  -- 1.1. substitute a = 1 (K1)
  have s1_1 : a + b = 1 + b := by (have h := congrArg (fun t : ℝ => t + b) hK1.1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 1.2. substitute b = 2 (K1)
  have s1_2 : 1 + b = 1 + 2 := by (have h := congrArg (fun t : ℝ => 1 + t) hK1.2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 1.3. calculation
  calc a + b = 1 + b := s1_1
    _ = 1 + 2 := s1_2
    _ = 3 := by norm_num

end Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnOpeningAssumeOfSeveralSentences
