module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/an-odd-factor-of-an-even-product.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnOddFactorOfAnEvenProduct.AnOddFactorOfAnEvenProduct

theorem an_odd_factor_of_an_even_product (a : ℤ) (b : ℤ) (hH3 : Odd a) (hH4 : Even (a * b)) :
    Even b := by
  -- 1. mun:even-product-factor, from H4
  have s1 : Even a ∨ Even b := by first | exact ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. mun:odd-not-even, from H3
  have s2 : ¬ Even a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := a) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := a) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := a) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := a) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := a) (by parley_side)); parley_side)
  -- 3. mun:disjunctive-syllogism-left, from 1, 2
  have s3 : Even b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even a) (Q := Even b) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even a) (Q := Even b) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even a) (Q := Even b) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even a) (Q := Even b) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even a) (Q := Even b) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even a) (Q := Even b) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.AnOddFactorOfAnEvenProduct.AnOddFactorOfAnEvenProduct
