module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-phrase-imported.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseImported.NotTriangularSaidTwoWays

theorem not_triangular_said_two_ways (hH1 : ¬ ((0 : ℤ) < 4 ∧ (∃ k : ℤ, 0 < k ∧ 4 = (k : ℚ) * ((k : ℚ) + 1) / 2))) :
    ¬ ((0 : ℤ) < 4 ∧ (∃ k : ℤ, 0 < k ∧ 4 = (k : ℚ) * ((k : ℚ) + 1) / 2)) := by
  -- 1. restate H1
  exact hH1

end Parley.Tests.Elaborator.APhraseImported.NotTriangularSaidTwoWays
