module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
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
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotient

theorem divide_by_a_square_of_a_quotient (j : ℤ) (hH1 : 0 < j) :
    1 / (1 / (j : ℚ)) ^ 2 = (j : ℚ) ^ 2 := by
  -- 1. algebra
  have hz1 : (j : ℚ) ≠ 0 := (by positivity); field

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotient
