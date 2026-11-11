module

public import NormTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.ProductNonzero

theorem product_nonzero (x : ℝ) (y : ℝ) (hH3 : x ≠ 0) (hH4 : y ≠ 0) :
    x * y ≠ 0 := by
  -- the theorem. contradiction
  intro hS
  -- 1. algebra, from S
  have s1 : x * y = 0 * y := by linear_combination (norm := parley_norm) hS
  -- 2. mun:multiply-cancel a := x, b := 0, c := y, from H4, 1
  have s2 : x = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) hH4)
  exact hH3 s2

end Parley.Proofs.Hammack.SumOfFactorialQuotients.ProductNonzero
