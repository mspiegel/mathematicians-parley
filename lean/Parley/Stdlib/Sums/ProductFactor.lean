module

public import InstanceTactics
public import NormTactics
public import SetTactics
public import SubstTactics
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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sums.ProductFactor

theorem product_factor (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) (c : ℤ) :
    (∏ᶠ x ∈ X, (x * c : ℤ)) = c ^ X.ncard * (∏ᶠ x ∈ X, (x : ℤ)) := by
  -- 1. proof
  have s1 : ∀ x ∈ X, True := by
    intro x hK1
    -- 1.1. mun:in-subset, from H1, K1
    -- 1.2. membership, from 1.1
    exact trivial
  -- 2. mun:product-of-products, from H2, 1
  have s2 : (∏ᶠ x ∈ X, (x * c : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) * (∏ᶠ x ∈ X, (c : ℤ)) := by
    have hI : (∏ᶠ a ∈ X, (a * c : ℤ)) = (∏ᶠ a ∈ X, (a : ℤ)) * (∏ᶠ a ∈ X, (c : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := (fun x : ℤ => c)) (X := X) hH2))
    exact hI
  -- 3. substitute
  have s3 : (∏ᶠ x ∈ X, (x * c : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) * c ^ X.ncard := by
    have c1 : (∏ᶠ x ∈ X, (c : ℤ)) = c ^ X.ncard := by exact (Parley.Items.Stdlib.Sums.mun_product_constant (X := X) hH2 (c := c))
    have row1 : (∏ᶠ x ∈ X, (x * c : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) * c ^ X.ncard := by parley_subst_at c1 s2
    exact row1
  -- 4. mun:product-integer, from H1, H2
  -- 5. mun:card-nat0, from H2
  have s5 : 0 ≤ (X.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2)
  -- 6. algebra, from 3
  linear_combination (norm := parley_norm) s3

end Parley.Stdlib.Sums.ProductFactor
