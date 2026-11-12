module

public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
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
  have s1 : x ≤ -1 := by linarith only [hS]
  -- 2. mun:square-nonneg
  have s2 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 3. inequalities
  have s3 : -x ≥ 1 := by linarith only [s1]
  -- 4. inequalities, from 2, 3
  have s4 : x ^ 2 - x > 0 := by linarith only [s2, s3]
  -- 5. inequalities, from 1
  have s5 : x + 1 ≤ 0 := by linarith only [s1]
  -- 6. mun:multiply-le x := x + 1, y := 0, c := x² − x, from 4, 5
  have s6 : (x ^ 2 - x) * (x + 1) ≤ (x ^ 2 - x) * 0 := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := x + 1) (y := (0 : ℝ)) (c := x ^ 2 - x) s5 s4)
  -- 7. inequalities
  have s7 : x ^ 3 - x ≤ 0 := by linarith only [s6]
  -- 8. inequalities, from 7
  have s8 : ¬ x ^ 3 - x > 0 := by linarith only [s7]
  exact s8 hH2

end Parley.Proofs.Hammack.CubicAboveMinusOne.CubicAboveMinusOne
