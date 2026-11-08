module

public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/cubic-above-minus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubicAboveMinusOne.CubicAboveMinusOne

theorem cubic_above_minus_one (x : ℝ) (hH2 : x ^ 3 - x > 0) :
    x > -1 := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. inequalities, from S
  have s1 : x ≤ -1 := by parley_order
  -- 2. mun:square-nonneg
  have s2 : x ^ 2 ≥ 0 := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 3. inequalities
  have s3 : -x ≥ 1 := by parley_order
  -- 4. inequalities, from 2, 3
  have s4 : x ^ 2 - x > 0 := by parley_order
  -- 5. inequalities, from 1
  have s5 : x + 1 ≤ 0 := by parley_order
  -- 6. mun:multiply-le x := x + 1, y := 0, c := x² − x, from 4, 5
  have s6 : (x ^ 2 - x) * (x + 1) ≤ (x ^ 2 - x) * 0 := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := x + 1) (y := (0 : ℝ)) (c := x ^ 2 - x) (by parley_side) (by parley_side))
  -- 7. inequalities
  have s7 : x ^ 3 - x ≤ 0 := by parley_order
  -- 8. inequalities, from 7
  have s8 : ¬ x ^ 3 - x > 0 := by parley_side
  exact s8 hH2

end Parley.Proofs.Hammack.CubicAboveMinusOne.CubicAboveMinusOne
