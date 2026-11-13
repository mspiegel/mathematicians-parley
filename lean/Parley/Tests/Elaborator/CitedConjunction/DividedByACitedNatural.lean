module

public import AlgebraTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/cited-conjunction.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitedConjunction.DividedByACitedNatural

theorem divided_by_a_cited_natural (a : ℤ) (hH1 : 0 < a) (k : ℤ) (hH3 : (0 < k ∧ (∃ m : ℤ, 0 < m ∧ (m : ℚ) = (a : ℚ) / (k : ℚ))) ∧ a > 1) :
    ((a : ℚ) / (k : ℚ)) ^ 2 = (a : ℚ) ^ 2 / (k : ℚ) ^ 2 := by
  -- 1. algebra, from H3
  parley_ring

end Parley.Tests.Elaborator.CitedConjunction.DividedByACitedNatural
