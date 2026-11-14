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

namespace Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnAssumeLineOfSeveralSentences

theorem an_assume_line_of_several_sentences (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    a + b = 3 := by
  -- 1. substitute a = 1 (H3)
  have s1 : a + b = 1 + b := congrArg (fun t : ℝ => t + b) hH3a
  -- 2. substitute b = 2 (H3)
  have s2 : 1 + b = 1 + 2 := congrArg (fun t : ℝ => 1 + t) hH3b
  -- 3. calculation
  calc a + b = 1 + b := s1
    _ = 1 + 2 := s2
    _ = 3 := by norm_num

end Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnAssumeLineOfSeveralSentences
