module

public import Tactics
public import Parley.Proofs.Hammack.PolynomialSign.NegativePowers

/-! Written from proofs/hammack/polynomial-sign.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PolynomialSign.QuinticFive

theorem quintic_five (x : ℝ) (hH2 : x ^ 5 - 4 * x ^ 4 + 3 * x ^ 3 - x ^ 2 + 3 * x - 4 ≥ 0) :
    x ≥ 0 := by
  -- the theorem. contradiction
  have sThm : x ≥ 0 := by
    by_contra hc_hS
    have hS : ¬ x ≥ 0 := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : x < 0 := by parley_side
    -- 2. thm:negative-powers, from 1
    have s2a : x ^ 2 ≥ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).1] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).1 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).1; parley_side)
    have s2b : x ^ 3 ≤ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.1] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.1 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.1; parley_side)
    have s2c : x ^ 4 ≥ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.1] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.1 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.1; parley_side)
    have s2d : x ^ 5 ≤ 0 := by first | linarith [(Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.2] | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.2 | (have h := (Parley.Proofs.Hammack.PolynomialSign.NegativePowers.negative_powers (x := x) (by parley_side)).2.2.2; parley_side)
    -- 3. inequalities
    have s3 : -(4 * x ^ 4) ≤ 0 := by parley_side
    -- 4. inequalities
    have s4 : 3 * x ^ 3 ≤ 0 := by parley_side
    -- 5. inequalities
    have s5 : -(x ^ 2) ≤ 0 := by parley_side
    -- 6. inequalities
    have s6 : 3 * x < 0 := by parley_side
    -- 7. inequalities, from 2, 3, 4, 5, 6
    have s7 : x ^ 5 - 4 * x ^ 4 + 3 * x ^ 3 - x ^ 2 + 3 * x - 4 < 0 := by parley_side
    -- 8. inequalities, from 7
    have s8 : ¬ x ^ 5 - 4 * x ^ 4 + 3 * x ^ 3 - x ^ 2 + 3 * x - 4 ≥ 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.PolynomialSign.QuinticFive
