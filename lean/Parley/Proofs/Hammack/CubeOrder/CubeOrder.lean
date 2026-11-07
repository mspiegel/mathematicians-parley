module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/cube-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeOrder.CubeOrder

set_option maxHeartbeats 400000 in
theorem cube_order (x : ℝ) (y : ℝ) (hH3 : x ^ 3 < y ^ 3) :
    x < y := by
  -- the theorem. contradiction
  have sThm : x < y := by
    by_contra hc_hS
    have hS : ¬ x < y := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : y ≤ x := by parley_order
    -- 2. inequalities
    have s2 : x - y ≥ 0 := by parley_order
    -- 3. mun:square-nonneg x := x + y/2
    have s3 : (x + y / 2) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2)); parley_side)
    -- 4. mun:square-nonneg x := y
    have s4 : y ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y)); parley_side)
    -- 5. inequalities
    have s5 : 3 * y ^ 2 / 4 ≥ 0 := by parley_order
    -- 6. inequalities, from 3, 5
    have s6 : (x + y / 2) ^ 2 + 3 * y ^ 2 / 4 ≥ 0 := by parley_order
    -- 7. algebra
    have s7 : x ^ 2 + x * y + y ^ 2 = (x + y / 2) ^ 2 + 3 * y ^ 2 / 4 := by parley_ring
    -- 8. transitivity, from 7, 6
    have s8 : x ^ 2 + x * y + y ^ 2 ≥ 0 := by parley_order
    -- 9. mun:product-nonneg x := x − y, y := x² + x·y + y², from 2, 8
    have s9 : (x - y) * (x ^ 2 + x * y + y ^ 2) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) (by parley_side) (by parley_side)); parley_side)
    -- 10. algebra
    have s10 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by parley_ring
    -- 11. transitivity, from 10, 9
    have s11 : x ^ 3 - y ^ 3 ≥ 0 := by parley_order
    -- 12. inequalities
    have s12 : x ^ 3 ≥ y ^ 3 := by parley_order
    -- 13. inequalities, from 12
    have s13 : ¬ x ^ 3 < y ^ 3 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.CubeOrder.CubeOrder
