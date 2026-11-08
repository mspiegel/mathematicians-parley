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

/-! Written from proofs/hammack/negative-quadratic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NegativeQuadratic.NegativeQuadratic

theorem negative_quadratic (x : ℝ) (hH2 : x ^ 2 + 5 * x < 0) :
    x < 0 := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. inequalities, from S
  have s1 : x ≥ 0 := by parley_order
  -- 2. mun:square-nonneg
  have s2 : x ^ 2 ≥ 0 := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 3. inequalities
  have s3 : 5 * x ≥ 0 := by parley_order
  -- 4. inequalities, from 2, 3
  have s4 : x ^ 2 + 5 * x ≥ 0 := by parley_order
  -- 5. inequalities, from 4
  have s5 : ¬ x ^ 2 + 5 * x < 0 := by parley_side
  exact s5 hH2

end Parley.Proofs.Hammack.NegativeQuadratic.NegativeQuadratic
