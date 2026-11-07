module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotient

theorem divide_by_a_square_of_a_quotient (j : ℤ) (hH1 : 0 < j) :
    1 / (1 / (j : ℚ)) ^ 2 = (j : ℚ) ^ 2 := by
  -- 1. algebra
  have s1 : 1 / (1 / (j : ℚ)) ^ 2 = (j : ℚ) ^ 2 := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotient
