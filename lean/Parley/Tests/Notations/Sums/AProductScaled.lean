module

public import NormTactics
public import PowerTactics
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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AProductScaled

theorem a_product_scaled (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) :
    (∏ᶠ x ∈ X, (x * 3 : ℤ)) = 3 ^ X.ncard * (∏ᶠ x ∈ X, (x : ℤ)) := by
  -- 1. thm:product-factor c := 3, from H1, H2
  first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ)))) | exact_mod_cast (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := X) hH1 hH2 (c := (3 : ℤ))); parley_set_side)

end Parley.Tests.Notations.Sums.AProductScaled
