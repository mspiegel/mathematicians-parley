module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
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

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.PairsEqualByArithmetic

theorem pairs_equal_by_arithmetic :
    (((1 + 1 : ℤ), (3 : ℤ)) : ℤ × ℤ) = ((2 : ℤ), (3 : ℤ)) := by
  -- 1. arithmetic
  exact Prod.ext (show (1 + 1 : ℤ) = 2 by norm_num) (show (3 : ℤ) = 3 by norm_num)

end Parley.Tests.Elaborator.PairsCompared.PairsEqualByArithmetic
