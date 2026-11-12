module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/quadratic-over-linear-diverges.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.QuadraticOverLinearDiverges.QuadraticOverLinearDiverges

theorem quadratic_over_linear_diverges (a : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → a n = (2 * (n : ℝ) ^ 2 + 1) / (3 * (n : ℝ) - 1)) :
    (∀ M : ℝ, ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n > N → a n > M)) := by
  -- 1. proof
  intro M
  -- 1.1. obtain N: thm:archimedean-natural x := 3M
  obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := 3 * M))
  -- 1.2. proof
  have s1_2 : ∀ n : ℤ, 0 < n → n > N → a n > M := by
    intro n hK2
    intro hA2
    -- 1.2.1. inequalities, from K2
    have s1_2_1 : n ≥ 1 := by linarith only [hK2]
    -- 1.2.2. inequalities, from K2
    have s1_2_2 : n > 0 := by linarith only [hK2]
    -- 1.2.3. inequalities
    have s1_2_3 : 3 * n - 1 ≥ 2 := by linarith only [s1_2_1]
    -- 1.2.4. inequalities, from 1.2.3
    have s1_2_4 : 3 * n - 1 > 0 := by linarith only [s1_2_3]
    -- 1.2.5. inequalities
    have s1_2_5 : 3 * n - 1 ≠ 0 := ne_of_gt (by linarith only [s1_2_4])
    -- 1.2.6. inequalities
    have s1_2_6 : (n : ℚ) ^ 2 - (n : ℚ) / 3 < (n : ℚ) ^ 2 := by linarith only [(show (n : ℚ) > 0 by exact_mod_cast s1_2_2)]
    -- 1.2.7. mun:square-nonneg x := n
    have s1_2_7 : n ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := n))
    -- 1.2.8. inequalities, from 1.2.7
    have s1_2_8 : 0 < n ^ 2 + 1 := by linarith only [s1_2_7]
    -- 1.2.9. inequalities
    have s1_2_9 : n ^ 2 < 2 * n ^ 2 + 1 := by linarith only [s1_2_8]
    -- 1.2.10. calculation
    have r64_1 : 3 * n - 1 ≠ 0 := by exact s1_2_5
    have s1_2_10 : (3 * (n : ℝ) - 1) * ((n : ℝ) / 3) < (3 * (n : ℝ) - 1) * a n := by
      calc (3 * (n : ℝ) - 1) * ((n : ℝ) / 3) = (n : ℝ) ^ 2 - (n : ℝ) / 3 := by parley_ring
        _ < (n : ℝ) ^ 2 := by parley_side
        _ < 2 * (n : ℝ) ^ 2 + 1 := by parley_side
        _ = (3 * (n : ℝ) - 1) * a n := by linear_combination (norm := parley_field) (-(3 * (n : ℝ)) + 1) * (hH2 n hK2)
    -- 1.2.11. mun:less-scaled x := n/3, y := a(n), c := 3n − 1, from 1.2.4, 1.2.10
    have s1_2_11 : (n : ℝ) / 3 < a n := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (n : ℝ) / 3) (y := a n) (c := 3 * (n : ℝ) - 1) (by exact_mod_cast gt_iff_lt.mp s1_2_4))).mpr s1_2_10
    -- 1.2.12. transitivity, from 1.1, A2
    have s1_2_12 : 3 * M < (n : ℝ) := by parley_order
    -- 1.2.13. inequalities
    have s1_2_13 : M < (n : ℝ) / 3 := by linarith only [s1_2_12]
    -- 1.2.14. transitivity, from 1.2.13, 1.2.11
    exact lt_trans s1_2_13 s1_2_11
  -- 1.3. exhibit, from 1.2
  exact ⟨N, s1_1a, s1_2⟩

end Parley.Proofs.Hammack.QuadraticOverLinearDiverges.QuadraticOverLinearDiverges
