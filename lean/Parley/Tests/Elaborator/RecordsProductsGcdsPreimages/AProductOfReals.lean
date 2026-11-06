module

public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfReals

theorem a_product_of_reals (n : ℤ) (hH2 : n ≥ 1) (t : ℤ → ℝ) :
    (∏ k ∈ Finset.Icc (1 : ℤ) (n + 1), (t k : ℝ)) = (∏ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) * t (n + 1) := by
  -- 1. mun:product-extended a := 1, from H2
  have s1 : (∏ k ∈ Finset.Icc (1 : ℤ) (n + 1), (t k : ℝ)) = (∏ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) * t (n + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfReals
