module

public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/scaled-gcd-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ScaledGcdBound.ScaledPairNotBothZero

theorem scaled_pair_not_both_zero (x : ℤ) (y : ℤ) (c : ℤ) (hH4 : ¬ (x = 0 ∧ y = 0)) (hH5 : c ≠ 0) :
    ¬ (c * x = 0 ∧ c * y = 0) := by
  -- the theorem. contradiction
  intro hS
  -- 1. contradiction
  have s1 : x = 0 := by
    by_contra (hS1 : x ≠ 0)
    -- 1.1. mun:product-nonzero x := c, y := x, from H5, S1
    have s1_1 : c * x ≠ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := x) hH5 hS1)
    exact s1_1 hS.1
  -- 2. contradiction
  have s2 : y = 0 := by
    by_contra (hS2 : y ≠ 0)
    -- 2.1. mun:product-nonzero x := c, from H5, S2
    have s2_1 : c * y ≠ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := c) (y := y) hH5 hS2)
    exact s2_1 hS.2
  -- 3. join 1, 2
  have s3 : x = 0 ∧ y = 0 := by parley_side
  exact hH4 s3

end Parley.Proofs.Hammack.ScaledGcdBound.ScaledPairNotBothZero
