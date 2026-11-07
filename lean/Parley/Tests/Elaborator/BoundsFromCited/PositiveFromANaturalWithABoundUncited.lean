module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/bounds-from-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundsFromCited.PositiveFromANaturalWithABoundUncited

theorem positive_from_a_natural_with_a_bound_uncited (n : ℤ) (hH1 : 0 < n) :
    (1 ≤ n ∧ n > 0) := by
  -- 1. inequalities, from H1
  have s1 : 1 ≤ n := by parley_order
  -- 2. inequalities, from H1
  have s2 : n > 0 := by parley_order
  -- 3. join 1, 2
  have s3 : 1 ≤ n ∧ n > 0 := by parley_side
  all_goals exact s3

end Parley.Tests.Elaborator.BoundsFromCited.PositiveFromANaturalWithABoundUncited
