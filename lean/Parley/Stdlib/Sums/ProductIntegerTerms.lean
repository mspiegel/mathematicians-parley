module

public import SetTactics
public import Sets
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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sums.ProductIntegerTerms

theorem product_integer_terms {α : Type*} (X : Set α) (hH2 : X.Finite) (t : α → ℤ) (hH3 : Set.MapsTo t X (Set.univ : Set ℤ)) :
    (∀ Y ∈ 𝒫 X, True) := by
  -- 1. induction on Y starting at ∅
  have r34_1 : X.Finite := by parley_set_side
  refine LeanBridges.Sets.subset_induction (by parley_finite) ?_ ?_
  · skip
    -- 1.1. mun:product-empty
    have s1_1 : (∏ᶠ x ∈ (∅ : Set α), (t x : ℤ)) = 1 := by exact (Parley.Items.Stdlib.Sums.mun_product_empty (X := X) (t := t))
    -- 1.2. membership, from 1.1
    exact trivial
  · intro Y hK hIH
    intro a hK2
    -- 1.3. def:difference u := a, Y := X, Z := Y, from K2
    have s1_3 : a ∈ X ∧ ¬ a ∈ Y := ((Parley.Items.Stdlib.Sets.def_difference (Y := X) (Z := Y) (u := a))).mp hK2
    -- 1.4. mun:finite-part, from H2, K
    have s1_4 : Y.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := Y) hH2 hK)
    -- 1.5. mun:product-add-one, from K, 1.3, 1.4
    have s1_5 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (t x : ℤ)) = (∏ᶠ x ∈ Y, (t x : ℤ)) * t a := by exact (Parley.Items.Stdlib.Sums.mun_product_add_one (t := t) (X := X) (Y := Y) (a := a) (by parley_set_side) s1_4 s1_3.1 s1_3.2)
    -- 1.6. mun:function-value f := t, D := X, E := ℤ, x := a, from H3, 1.3
    -- 1.7. membership, from IH, 1.5, 1.6
    exact trivial

end Parley.Stdlib.Sums.ProductIntegerTerms
