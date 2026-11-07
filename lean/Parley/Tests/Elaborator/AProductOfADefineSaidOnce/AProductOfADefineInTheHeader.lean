module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-product-of-a-define-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductOfADefineSaidOnce.AProductOfADefineInTheHeader

theorem a_product_of_a_define_in_the_header (p : ℤ) (hH1 : 0 < p) (e : ℤ → ℤ) (hD1 : ∀ i : ℤ, i ∈ Finset.Icc (1 : ℤ) (1 : ℤ) → e i = p) :
    (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = p := by
  -- 1. mun:product-single a := 1, t := e
  have s1 : (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = e 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))); parley_side)
  -- 2. D1
  have r44_1 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) (1 : ℤ) := by parley_side
  have s2 : e 1 = p := by (try simp only [hD1]); first | done | parley_side
  -- 3. calculation
  have s3 : (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = p := by
    calc (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = e 1 := by parley_side
      _ = p := by parley_side
  all_goals exact s3

end Parley.Tests.Elaborator.AProductOfADefineSaidOnce.AProductOfADefineInTheHeader
