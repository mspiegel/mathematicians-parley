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
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeDivisor

theorem a_negative_divisor :
    (-3 : ℤ) ∣ (9 : ℤ) := by
  -- 1. arithmetic
  norm_num

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeDivisor
