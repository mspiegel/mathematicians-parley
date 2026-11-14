module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.OneIsNotEven

theorem one_is_not_even :
    ¬ Even (1 : ℤ) := by
  -- 1. arithmetic
  norm_num

end Parley.Tests.Notations.Divisibility.OneIsNotEven
