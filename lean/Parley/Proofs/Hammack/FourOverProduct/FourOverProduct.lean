module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/four-over-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FourOverProduct.FourOverProduct

theorem four_over_product (x : ℝ) (hH2 : 0 < x) (hH3 : x < 4) :
    4 / (x * (4 - x)) ≥ 1 := by
  -- 1. inequalities
  have s1 : 0 < 4 - x := by linarith only [hH3]
  -- 2. mun:less-scaled x := 0, y := 4 − x, c := x, from H2, 1
  have s2 : x * 0 < x * (4 - x) := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := 4 - x) (c := x) hH2)).mp s1
  -- 3. inequalities, from 2
  have s3 : 0 < x * (4 - x) := by linarith only [s2]
  -- 4. mun:square-nonneg x := x − 2
  have s4 : (x - 2) ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x - 2))
  -- 5. algebra
  have s5 : (x - 2) ^ 2 = 4 - x * (4 - x) := by parley_ring
  -- 6. transitivity, from 4, 5
  have s6 : 0 ≤ 4 - x * (4 - x) := by parley_order
  -- 7. inequalities
  have s7 : x * (4 - x) ≤ 4 := by linarith only [s6]
  -- 8. mun:divide-le x := x·(4 − x), y := 4, c := x·(4 − x), from 3, 7
  have s8 : x * (4 - x) / (x * (4 - x)) ≤ 4 / (x * (4 - x)) := by exact (Parley.Items.Stdlib.Numbers.mun_divide_le (x := x * (4 - x)) (y := (4 : ℝ)) (c := x * (4 - x)) s7 s3)
  -- 9. algebra
  have r42_1 : 0 ≠ x * (4 - x) := ne_of_lt (by linarith only [s3])
  have s9 : x * (4 - x) / (x * (4 - x)) = 1 := by parley_ring
  -- 10. transitivity, from 9, 8
  have r46_1 : 0 ≠ x * (4 - x) := ne_of_lt (by linarith only [s3])
  exact Eq.trans_le s9.symm s8

end Parley.Proofs.Hammack.FourOverProduct.FourOverProduct
