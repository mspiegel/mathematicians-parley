module

public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-product-over-a-part-of-a-domain.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductOverAPartOfADomain.AProductOverAPartOfADomain

theorem a_product_over_a_part_of_a_domain (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (L : Set ℤ) (hH2 : L ⊆ X) (hH3 : L.Finite) (f : ℤ → ℤ) (hH4 : Set.MapsTo f X (Set.univ : Set ℤ)) (hH5 : ∀ x ∈ L, True) (hH6 : ∀ x ∈ L, True) :
    (∏ᶠ x ∈ L, (x * f x : ℤ)) = (∏ᶠ x ∈ L, (x : ℤ)) * (∏ᶠ x ∈ L, (f x : ℤ)) := by
  -- 1. mun:product-of-products, from H3, H5, H6
  have hI : (∏ᶠ a ∈ L, (a * f a : ℤ)) = (∏ᶠ a ∈ L, (a : ℤ)) * (∏ᶠ a ∈ L, (f a : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) hH3))
  exact hI

end Parley.Tests.Elaborator.AProductOverAPartOfADomain.AProductOverAPartOfADomain
