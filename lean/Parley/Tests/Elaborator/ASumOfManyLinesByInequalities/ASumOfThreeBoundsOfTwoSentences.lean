module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-sum-of-many-lines-by-inequalities.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfThreeBoundsOfTwoSentences

theorem a_sum_of_three_bounds_of_two_sentences (P : ℝ) (Q : ℝ) (R : ℝ) (M : ℝ) (hH5 : P > 0 ∧ P > M) (hH6 : Q > 0 ∧ Q ≥ 0) (hH7 : R > 0 ∧ R ≥ 0) :
    P + Q + R > M := by
  -- 1. inequalities, from H5, H6, H7
  linarith only [hH5.2, hH6.1, hH7.1]

end Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfThreeBoundsOfTwoSentences
