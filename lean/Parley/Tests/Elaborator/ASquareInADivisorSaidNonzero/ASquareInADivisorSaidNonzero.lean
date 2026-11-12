module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-square-in-a-divisor-said-nonzero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ASquareInADivisorSaidNonzero

theorem a_square_in_a_divisor_said_nonzero (x : ℝ) (y : ℝ) (hH3 : y = 1 / (1 + x ^ 2)) (hH4 : 1 / (1 + x ^ 2) ≥ 0) :
    y ≥ 0 := by
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 2. inequalities, from 1
  have s2 : 1 + x ^ 2 > 0 := by linarith only [s1]
  -- 3. transitivity, from H3, H4
  have r17_1 : 1 + x ^ 2 ≠ 0 := ne_of_gt (by linarith only [s2])
  parley_order

end Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ASquareInADivisorSaidNonzero
