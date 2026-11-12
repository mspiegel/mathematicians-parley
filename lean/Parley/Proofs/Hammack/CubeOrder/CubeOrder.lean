module

public import AlgebraTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Basic
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

theorem cube_order (x : ℝ) (y : ℝ) (hH3 : x ^ 3 < y ^ 3) :
    x < y := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. inequalities, from S
  have s1 : y ≤ x := by linarith only [hS]
  -- 2. inequalities
  have s2 : x - y ≥ 0 := by linarith only [s1]
  -- 3. mun:square-nonneg x := x + y/2
  have s3 : (x + y / 2) ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2))
  -- 4. mun:square-nonneg x := y
  have s4 : y ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y))
  -- 5. inequalities
  have s5 : 3 * y ^ 2 / 4 ≥ 0 := by linarith only [s4]
  -- 6. inequalities, from 3, 5
  have s6 : (x + y / 2) ^ 2 + 3 * y ^ 2 / 4 ≥ 0 := by linarith only [s3, s5]
  -- 7. algebra
  have s7 : x ^ 2 + x * y + y ^ 2 = (x + y / 2) ^ 2 + 3 * y ^ 2 / 4 := by parley_ring
  -- 8. transitivity, from 7, 6
  have s8 : x ^ 2 + x * y + y ^ 2 ≥ 0 := by exact LE.le.trans_eq s6 s7.symm
  -- 9. mun:product-nonneg x := x − y, y := x² + x·y + y², from 2, 8
  have s9 : (x - y) * (x ^ 2 + x * y + y ^ 2) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) s2 s8)
  -- 10. algebra
  have s10 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by parley_ring
  -- 11. transitivity, from 10, 9
  have s11 : x ^ 3 - y ^ 3 ≥ 0 := by exact LE.le.trans_eq s9 s10.symm
  -- 12. inequalities
  have s12 : x ^ 3 ≥ y ^ 3 := by linarith only [s11]
  -- 13. inequalities, from 12
  have s13 : ¬ x ^ 3 < y ^ 3 := by linarith only [s12]
  exact s13 hH3

end Parley.Proofs.Hammack.CubeOrder.CubeOrder
