module

public import AlgebraTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/product-of-sequence-limits.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall

theorem bounded_times_small (C : ℝ) (u : ℝ) (K : ℝ) (d : ℝ) (hH5 : K > 0) (hH6 : abs C < K) (hH7 : abs u < d) :
    abs (C * u) < K * d := by
  -- 1. mun:abs-nonneg x := u
  have s1 : abs u ≥ 0 := by exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (u : ℂ)))
  -- 2. inequalities
  have s2 : K - abs C > 0 := by parley_order
  -- 3. inequalities
  have s3 : K - abs C ≥ 0 := by parley_order
  -- 4. mun:product-nonneg x := K − |C|, y := |u|, from 1, 3
  have s4 : (K - abs C) * abs u ≥ 0 := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := K - abs C) (y := abs u) (by parley_side) (by parley_side))
  -- 5. substitute
  have s5 : K * abs u - abs C * abs u ≥ 0 := by
    have c1 : (K - abs C) * abs u = K * abs u - abs C * abs u := by parley_ring
    have row1 : K * abs u - abs C * abs u ≥ 0 := by parley_subst_at c1 s4
    exact row1
  -- 6. inequalities
  have s6 : abs C * abs u ≤ K * abs u := by parley_order
  -- 7. calculation
  calc abs (C * u) = abs C * abs u := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u))
    _ ≤ K * abs u := by parley_side
    _ < K * d := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs u) (y := d) (c := K) (by parley_side))).mp hH7

end Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall
