module

public import ArithTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.ZeroDoesNotDivideFive

theorem zero_does_not_divide_five :
    ¬ (0 : ℤ) ∣ (5 : ℤ) := by
  -- 1. mun:zero-divides n := 5
  have s1 : (0 : ℤ) ∣ (5 : ℤ) ↔ (5 : ℤ) = 0 := by exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (5 : ℤ)))
  -- 2. arithmetic
  have s2 : (5 : ℤ) ≠ 0 := by parley_arith
  -- 3. mun:iff-not-from-right, from 1, 2
  exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := (0 : ℤ) ∣ (5 : ℤ)) (Q := (5 : ℤ) = 0) s1 s2)

end Parley.Tests.Notations.Divisibility.ZeroDoesNotDivideFive
