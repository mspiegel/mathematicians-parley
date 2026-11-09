module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Tests.Notations.Sums.AProductScaled

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AProductScaledCited

theorem a_product_scaled_cited (Y : Set ℤ) (hH1 : Y ⊆ (Set.univ : Set ℤ)) (hH2 : Y.Finite) :
    (∏ᶠ k ∈ Y, (k * 3 : ℤ)) = 3 ^ Y.ncard * (∏ᶠ k ∈ Y, (k : ℤ)) := by
  -- 1. thm:a-product-scaled X := Y, from H1, H2
  exact (Parley.Tests.Notations.Sums.AProductScaled.a_product_scaled (X := Y) (by parley_set_side) hH2)

end Parley.Tests.Notations.Sums.AProductScaledCited
