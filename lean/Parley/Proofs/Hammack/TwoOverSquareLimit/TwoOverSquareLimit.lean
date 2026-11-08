module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/two-over-square-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoOverSquareLimit.TwoOverSquareLimit

set_option maxHeartbeats 600000 in
theorem two_over_square_limit (a : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → a n = 5 + 2 / (n : ℝ) ^ 2) :
    Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds 5) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 5) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 2 > 0 := by parley_order
    -- 1.2. obtain N: thm:archimedean x := ε/2, from 1.1
    obtain ⟨N, s1_2a, s1_2b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε / 2) s1_1)
    -- 1.3. proof
    have s1_3 : ∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 5) < ε := by
      intro n hK2
      intro hA2
      -- 1.3.1. inequalities, from K2
      have s1_3_1 : n > 0 := by parley_order
      -- 1.3.2. inequalities, from K2
      have s1_3_2 : n ≥ 1 := by parley_order
      -- 1.3.3. mun:multiply-le x := 1, y := n, c := n, from 1.3.2
      have r41_1 : n > 0 := by parley_side
      have s1_3_3 : n * 1 ≤ n * n := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side))
      -- 1.3.4. algebra
      have s1_3_4 : n * n = n ^ 2 := by parley_ring
      -- 1.3.5. transitivity, from 1.3.3, 1.3.4
      have s1_3_5 : n ≤ n ^ 2 := by parley_order
      -- 1.3.6. transitivity, from 1.3.1, 1.3.5
      have s1_3_6 : n ^ 2 > 0 := by parley_order
      -- 1.3.7. mun:reciprocal-order x := n, y := n², from 1.3.5
      have r54_1 : n > 0 := by parley_side
      have r54_2 : n ^ 2 > 0 := by parley_side
      have s1_3_7 : 1 / (n : ℚ) ^ 2 ≤ 1 / (n : ℚ) := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (n : ℚ)) (by parley_side) (y := (n : ℚ) ^ 2) (by parley_side))).mp (by parley_side)
      -- 1.3.8. mun:reciprocal-order x := N, y := n, from A2
      have r59_1 : N > 0 := by parley_order
      have r59_2 : n > 0 := by parley_side
      have s1_3_8 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side)
      -- 1.3.9. inequalities
      have s1_3_9 : 2 * (1 / (n : ℚ) ^ 2) ≤ 2 * (1 / (n : ℚ)) := by parley_order
      -- 1.3.10. inequalities
      have s1_3_10 : 2 * (1 / (n : ℚ)) ≤ 2 * (1 / (N : ℚ)) := by parley_order
      -- 1.3.11. inequalities
      have s1_3_11 : 2 * (1 / (N : ℝ)) < ε := by parley_order
      -- 1.3.12. algebra, from H2
      have s1_3_12 : a n - 5 = 2 * (1 / (n : ℝ) ^ 2) := by linear_combination (norm := parley_field) (hH2 n (by parley_side))
      -- 1.3.13. transitivity, from 1.3.12, 1.3.9, 1.3.10, 1.3.11
      have s1_3_13 : a n - 5 < ε := by parley_order
      -- 1.3.14. mun:reciprocal-positive x := n², from 1.3.6
      have s1_3_14 : 1 / (n : ℚ) ^ 2 > 0 := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ) ^ 2) (by parley_side))
      -- 1.3.15. inequalities
      have s1_3_15 : 2 * (1 / (n : ℚ) ^ 2) > 0 := by parley_order
      -- 1.3.16. transitivity, from 1.3.15, 1.3.12
      have s1_3_16 : 0 < a n - 5 := by parley_order
      -- 1.3.17. def:abs x := a(n) − 5
      have r99_2 : 0 ≤ a n - 5 := by parley_side
      have s1_3_17 : abs (a n - 5) = a n - 5 := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a n - 5)) (by parley_side)
      -- 1.3.18. transitivity, from 1.3.17, 1.3.13
      parley_order
    -- 1.4. exhibit, from 1.3
    exact ⟨N, s1_2a, s1_3⟩
  -- 2. def:tends-to L := 5, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (5 : ℝ)))).mpr s1

end Parley.Proofs.Hammack.TwoOverSquareLimit.TwoOverSquareLimit
