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
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AProductScaled

theorem a_product_scaled (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) :
    (∏ᶠ x ∈ X, (x * 3 : ℤ)) = 3 ^ X.ncard * (∏ᶠ x ∈ X, (x : ℤ)) := by
  -- 1. thm:product-factor c := 3, from H1, H2
  exact (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ)))

end Parley.Tests.Notations.Sums.AProductScaled
