module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/product-step-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductStepBound.ProductStepBound

theorem product_step_bound (t : ℝ) (p : ℝ) (hH3 : 0 < t) (hH4 : t ≤ 1 / 4) (hH5 : p ≥ 1 / 4 + t) :
    p * (1 - t) ≥ 1 / 4 + t / 2 := by
  -- 1. inequalities
  have s1 : 3 / 4 ≤ 1 - t := by linarith only [hH4]
  -- 2. inequalities, from 1
  have s2 : 0 < 1 - t := by linarith only [s1]
  -- 3. mun:multiply-le x := 1/4 + t, y := p, c := 1 − t, from H5, 2
  have s3 : (1 - t) * (1 / 4 + t) ≤ (1 - t) * p := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := 1 / 4 + t) (y := p) (c := 1 - t) hH5 s2)
  -- 4. algebra
  have s4 : (1 - t) * (1 / 4 + t) = 1 / 4 + t / 2 + t * (1 / 4 - t) := by parley_ring
  -- 5. inequalities
  have s5 : 0 ≤ 1 / 4 - t := by linarith only [hH4]
  -- 6. inequalities
  have s6 : t ≥ 0 := by linarith only [hH3]
  -- 7. mun:product-nonneg x := t, y := 1/4 − t, from 5, 6
  have s7 : t * (1 / 4 - t) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := t) (y := 1 / 4 - t) s6 s5)
  -- 8. inequalities
  have s8 : 1 / 4 + t / 2 + t * (1 / 4 - t) ≥ 1 / 4 + t / 2 := by linarith only [s7]
  -- 9. algebra
  have s9 : p * (1 - t) = (1 - t) * p := by parley_ring
  -- 10. transitivity, from 9, 3, 4, 8
  parley_order

end Parley.Proofs.Hammack.ProductStepBound.ProductStepBound
