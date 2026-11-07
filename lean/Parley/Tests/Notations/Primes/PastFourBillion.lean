module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.PastFourBillion

theorem past_four_billion :
    (641 : ℤ) ∣ (2 ^ 32 + 1 : ℤ) := by
  -- 1. arithmetic
  have s1 : (641 : ℤ) ∣ (2 ^ 32 + 1 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Primes.PastFourBillion
