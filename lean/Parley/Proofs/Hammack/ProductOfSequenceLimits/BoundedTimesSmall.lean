module

public import AlgebraTactics
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
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
  have s1 : abs u ≥ 0 := by
    have hI : 0 ≤ abs u := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (u : ℂ))))
    exact hI
  -- 2. inequalities
  have s2 : K - abs C > 0 := by linarith only [hH6]
  -- 3. inequalities
  have s3 : K - abs C ≥ 0 := by linarith only [s2]
  -- 4. mun:product-nonneg x := K − |C|, y := |u|, from 1, 3
  have s4 : (K - abs C) * abs u ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := K - abs C) (y := abs u) s3 s1)
  -- 5. substitute
  have s5 : K * abs u - abs C * abs u ≥ 0 := by
    have c1 : (K - abs C) * abs u = K * abs u - abs C * abs u := by parley_ring
    have row1 : K * abs u - abs C * abs u ≥ 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t ≥ 0)) c1 s4; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 6. inequalities
  have s6 : abs C * abs u ≤ K * abs u := by linarith only [s5]
  -- 7. calculation
  calc abs (C * u) = abs C * abs u := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u))
    _ ≤ K * abs u := by exact s6
    _ < K * d := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs u) (y := d) (c := K) hH5)).mp hH7

end Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall
