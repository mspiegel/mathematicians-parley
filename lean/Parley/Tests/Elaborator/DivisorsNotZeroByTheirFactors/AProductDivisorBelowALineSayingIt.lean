module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.AProductDivisorBelowALineSayingIt

theorem a_product_divisor_below_a_line_saying_it (k : ℤ) (hH2 : k > 0) :
    (k * (k + 1) ≠ 0 ∧ 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1))) := by
  -- 1. inequalities, from H2
  have s1 : k + 1 > 0 := by linarith only [hH2]
  -- 2. mun:product-nonzero x := k, y := k + 1
  have r46_1 : k ≠ 0 := ne_of_gt (by linarith only [hH2])
  have r46_2 : k + 1 ≠ 0 := ne_of_gt (by linarith only [s1])
  have s2 : k * (k + 1) ≠ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := k) (y := k + 1) r46_1 r46_2)
  -- 3. algebra
  have r51_1 : k ≠ 0 := ne_of_gt (by linarith only [hH2])
  have r51_2 : k + 1 ≠ 0 := ne_of_gt (by linarith only [s1])
  have s3 : 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1)) := by parley_ring
  -- 4. join 2, 3
  have s4 : k * (k + 1) ≠ 0 ∧ 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1)) := by parley_side
  exact ⟨(s4).1, (s4).2⟩

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.AProductDivisorBelowALineSayingIt
