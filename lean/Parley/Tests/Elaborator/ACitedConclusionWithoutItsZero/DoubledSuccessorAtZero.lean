module

public import Mathlib.Algebra.Group.Monoid
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
public import Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor

/-! Written from tests/elaborator/a-cited-conclusion-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessorAtZero

theorem doubled_successor_at_zero :
    (2 * 1 : ℤ) = 2 * 0 + 2 := by
  -- 1. thm:doubled-successor n := 0
  simpa only [mul_one, zero_add] using (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := (0 : ℤ)) (by norm_num))

end Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessorAtZero
