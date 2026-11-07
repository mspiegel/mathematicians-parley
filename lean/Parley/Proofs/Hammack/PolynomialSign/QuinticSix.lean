module

public import ArithTactics
public import OrderTactics
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

namespace Parley.Proofs.Hammack.PolynomialSign.QuinticSix

theorem quintic_six (x : ℝ) (hH2 : x ^ 5 + 7 * x ^ 3 + 5 * x ≥ x ^ 4 + x ^ 2 + 8) :
    x ≥ 0 := by
  -- the theorem. contradiction
  have sThm : x ≥ 0 := by
    by_contra hc_hS
    have hS : ¬ x ≥ 0 := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : x < 0 := by parley_order
    -- 2. thm:negative-powers, from 1
    have s2a : x ^ 2 ≥ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).1] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).1 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).1; parley_side)
    have s2b : x ^ 3 ≤ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.1] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.1 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.1; parley_side)
    have s2c : x ^ 4 ≥ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.1] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.1 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.1; parley_side)
    have s2d : x ^ 5 ≤ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.2] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.2 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) s1).2.2.2; parley_side)
    -- 3. inequalities
    have s3 : 7 * x ^ 3 ≤ 0 := by parley_order
    -- 4. inequalities
    have s4 : 5 * x < 0 := by parley_order
    -- 5. inequalities, from 2, 3, 4
    have s5 : x ^ 5 + 7 * x ^ 3 + 5 * x < x ^ 4 + x ^ 2 + 8 := by parley_order
    -- 6. inequalities, from 5
    have s6 : ¬ x ^ 5 + 7 * x ^ 3 + 5 * x ≥ x ^ 4 + x ^ 2 + 8 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.PolynomialSign.QuinticSix
