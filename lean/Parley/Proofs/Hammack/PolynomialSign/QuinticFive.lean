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
public import Parley.Proofs.Hammack.PolynomialSign.NegativePowers

/-! Written from proofs/hammack/polynomial-sign.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PolynomialSign.QuinticFive

theorem quintic_five (x : ℝ) (hH2 : x ^ 5 - 4 * x ^ 4 + 3 * x ^ 3 - x ^ 2 + 3 * x - 4 ≥ 0) :
    x ≥ 0 := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. inequalities, from S
  have s1 : x < 0 := by linarith only [hS]
  -- 2. thm:negative-powers, from 1
  have s2a : x ^ 2 ≥ 0 := by exact (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).1
  have s2b : x ^ 3 ≤ 0 := by exact (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.1
  have s2c : x ^ 4 ≥ 0 := by exact (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.1
  have s2d : x ^ 5 ≤ 0 := by exact (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.2
  -- 3. inequalities
  have s3 : -(4 * x ^ 4) ≤ 0 := by linarith only [s2c]
  -- 4. inequalities
  have s4 : 3 * x ^ 3 ≤ 0 := by linarith only [s2b]
  -- 5. inequalities
  have s5 : -(x ^ 2) ≤ 0 := by linarith only [s2a]
  -- 6. inequalities
  have s6 : 3 * x < 0 := by linarith only [s1]
  -- 7. inequalities, from 2, 3, 4, 5, 6
  have s7 : x ^ 5 - 4 * x ^ 4 + 3 * x ^ 3 - x ^ 2 + 3 * x - 4 < 0 := by linarith only [s2d, s3, s4, s5, s6]
  -- 8. inequalities, from 7
  have s8 : ¬ x ^ 5 - 4 * x ^ 4 + 3 * x ^ 3 - x ^ 2 + 3 * x - 4 ≥ 0 := by linarith only [s7]
  exact s8 hH2

end Parley.Proofs.Hammack.PolynomialSign.QuinticFive
