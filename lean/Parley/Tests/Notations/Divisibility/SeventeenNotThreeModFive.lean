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
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.SeventeenNotThreeModFive

theorem seventeen_not_three_mod_five :
    ¬ (17 : ℤ) ≡ (3 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. arithmetic
  norm_num

end Parley.Tests.Notations.Divisibility.SeventeenNotThreeModFive
