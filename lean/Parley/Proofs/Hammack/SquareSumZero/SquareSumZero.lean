module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/square-sum-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareSumZero.SquareSumZero

theorem square_sum_zero (x : ℝ) (y : ℝ) :
    ((x + y) ^ 2 = x ^ 2 + y ^ 2 ↔ x = 0 ∨ y = 0) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. algebra, from D1
    have s1 : x * y = 0 := by linear_combination (norm := parley_norm) ((1 / 2 : ℝ)) * hD1
    -- 2. mun:zero-product, from 1
    exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := x) (y := y))).mp s1
  · skip
    intro hD2
    -- 3. cases, from D2
    rcases hD2 with hC1 | hC2
    · skip
      -- 3.1. algebra, from C1
      linear_combination (norm := parley_norm) (2 * y) * hC1
    · skip
      -- 3.2. algebra, from C2
      linear_combination (norm := parley_norm) (2 * x) * hC2

end Parley.Proofs.Hammack.SquareSumZero.SquareSumZero
