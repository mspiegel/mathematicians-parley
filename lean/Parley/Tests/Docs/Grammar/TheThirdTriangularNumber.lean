module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Init
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

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.TheThirdTriangularNumber

theorem the_third_triangular_number :
    (3 * (3 + 1) / 2 : ℚ) = 6 := by
  -- 1. calculation
  calc (3 * (3 + 1) / 2 : ℚ) = 3 * (3 + 1) / 2 := rfl
    _ = 6 := by norm_num

end Parley.Tests.Docs.Grammar.TheThirdTriangularNumber
