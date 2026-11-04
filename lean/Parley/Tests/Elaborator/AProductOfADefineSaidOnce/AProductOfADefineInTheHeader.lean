module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-product-of-a-define-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductOfADefineSaidOnce.AProductOfADefineInTheHeader

theorem a_product_of_a_define_in_the_header (p : ℕ) (hH1 : 0 < p) (e : ℤ → ℤ) (hD1 : ∀ i : ℤ, i ∈ Finset.Icc (1 : ℤ) (1 : ℤ) → e i = (p : ℤ)) :
    (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = (p : ℤ) := by
  -- 1. mun:product-single a := 1, t := e
  have s1 : (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = e 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); parley_side)
  -- 2. D1
  have r44_1 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) (1 : ℤ) := by parley_side
  have s2 : e 1 = (p : ℤ) := by (try simp only [hD1]); first | done | parley_side
  -- 3. calculation
  have s3 : (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = (p : ℤ) := by
    calc (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = e 1 := by parley_side
      _ = (p : ℤ) := by parley_side
  all_goals exact s3

end Parley.Tests.Elaborator.AProductOfADefineSaidOnce.AProductOfADefineInTheHeader
