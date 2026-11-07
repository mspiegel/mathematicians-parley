module

public import AlgebraTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/product-of-sequence-limits.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall

theorem bounded_times_small (C : ℝ) (u : ℝ) (K : ℝ) (d : ℝ) (hH5 : K > 0) (hH6 : abs C < K) (hH7 : abs u < d) :
    abs (C * u) < K * d := by
  -- 1. mun:abs-nonneg x := u
  have s1 : abs u ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (u : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (u : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (u : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (u : ℂ))); parley_side)
  -- 2. inequalities
  have s2 : K - abs C > 0 := by parley_order
  -- 3. inequalities
  have s3 : K - abs C ≥ 0 := by parley_order
  -- 4. mun:product-nonneg x := K − |C|, y := |u|, from 1, 3
  have s4 : (K - abs C) * abs u ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := K - abs C) (y := abs u) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := K - abs C) (y := abs u) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := K - abs C) (y := abs u) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := K - abs C) (y := abs u) (by parley_side) (by parley_side)); parley_side)
  -- 5. substitute
  have s5 : K * abs u - abs C * abs u ≥ 0 := by
    have c1 : (K - abs C) * abs u = K * abs u - abs C * abs u := by parley_ring
    have row1 : K * abs u - abs C * abs u ≥ 0 := by parley_subst_at c1 s4
    exact row1
  -- 6. inequalities
  have s6 : abs C * abs u ≤ K * abs u := by parley_order
  -- 7. calculation
  have s7 : abs (C * u) < K * d := by
    calc abs (C * u) = abs C * abs u := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); parley_side)
      _ ≤ K * abs u := by parley_side
      _ < K * d := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs u) (y := d) (c := K) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs u) (y := d) (c := K) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs u) (y := d) (c := K) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs u) (y := d) (c := K) (by parley_side))).mp (by parley_side); parley_side)
  all_goals exact s7

end Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall
