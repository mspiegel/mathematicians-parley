module

public import AlgebraTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAProductWithAQuotient

theorem divide_by_a_product_with_a_quotient (j : ℤ) (hH1 : 0 < j) :
    1 / (2 * (1 / (j : ℚ))) = (j : ℚ) / 2 := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAProductWithAQuotient
