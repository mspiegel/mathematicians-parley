module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/rational-sequence-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSequenceLimit.RationalSequenceLimit

set_option maxHeartbeats 600000 in
theorem rational_sequence_limit (a : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → a n = (2 * (n : ℝ) + 1) / (3 * (n : ℝ) - 1)) :
    Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds (2 / 3)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 2 / 3) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) hA1)
    -- 1.2. proof
    have s1_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 2 / 3) < ε := by
      intro n hK2
      intro hA2
      -- 1.2.1. inequalities, from K2
      have s1_2_1 : n ≥ 1 := by parley_order
      -- 1.2.2. inequalities, from K2
      have s1_2_2 : n > 0 := by parley_order
      -- 1.2.3. inequalities
      have s1_2_3 : 3 * n - 1 ≥ 2 := by parley_order
      -- 1.2.4. inequalities, from 1.2.3
      have s1_2_4 : 3 * n - 1 > 0 := by parley_order
      -- 1.2.5. inequalities
      have s1_2_5 : 9 * n - 3 ≥ 5 * n + 1 := by parley_order
      -- 1.2.6. inequalities, from 1.2.5
      have s1_2_6 : 5 * n ≤ 9 * n - 3 := by parley_order
      -- 1.2.7. inequalities
      have s1_2_7 : 5 * n > 0 := by parley_order
      -- 1.2.8. transitivity, from 1.2.7, 1.2.6
      have s1_2_8 : 9 * n - 3 > 0 := by parley_order
      -- 1.2.9. inequalities
      have s1_2_9 : 9 * n - 3 ≠ 0 := by parley_side
      -- 1.2.10. algebra, from H2
      have r68_1 : 3 * n - 1 ≠ 0 := by parley_side
      have r68_2 : 9 * n - 3 ≠ 0 := by parley_side
      have s1_2_10 : a n - 2 / 3 = 5 * (1 / (9 * (n : ℝ) - 3)) := by linear_combination (norm := parley_field) ((3) / ((3))) * (hH2 n (by parley_side))
      -- 1.2.11. mun:reciprocal-positive x := 9n − 3, from 1.2.8
      have s1_2_11 : 1 / (9 * (n : ℚ) - 3) > 0 := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := 9 * (n : ℚ) - 3) (by parley_side))
      -- 1.2.12. inequalities
      have r76_1 : 9 * n - 3 ≠ 0 := by parley_side
      have s1_2_12 : 5 * (1 / (9 * (n : ℚ) - 3)) > 0 := by parley_order
      -- 1.2.13. transitivity, from 1.2.12, 1.2.10
      have r82_1 : 9 * n - 3 ≠ 0 := by parley_side
      have s1_2_13 : a n - 2 / 3 > 0 := by parley_order
      -- 1.2.14. inequalities
      have s1_2_14 : a n > 2 / 3 := by parley_order
      -- 1.2.15. inequalities
      have s1_2_15 : 2 / 3 - ε < 2 / 3 := by parley_order
      -- 1.2.16. transitivity, from 1.2.15, 1.2.14
      have s1_2_16 : 2 / 3 - ε < a n := by parley_order
      -- 1.2.17. mun:reciprocal-order x := 5n, y := 9n − 3, from 1.2.6
      have r103_1 : 5 * n > 0 := by parley_side
      have r103_2 : 9 * n - 3 > 0 := by parley_side
      have s1_2_17 : 1 / (9 * (n : ℚ) - 3) ≤ 1 / (5 * (n : ℚ)) := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 5 * (n : ℚ)) (by parley_side) (y := 9 * (n : ℚ) - 3) (by parley_side))).mp (by parley_side)
      -- 1.2.18. inequalities
      have r108_1 : 9 * n - 3 ≠ 0 := by parley_side
      have s1_2_18 : 5 * (1 / (9 * (n : ℚ) - 3)) ≤ 5 * (1 / (5 * (n : ℚ))) := by parley_order
      -- 1.2.19. algebra
      have s1_2_19 : 5 * (1 / (5 * (n : ℚ))) = 1 / (n : ℚ) := by parley_ring
      -- 1.2.20. mun:reciprocal-order x := N, y := n, from A2
      have r117_1 : N > 0 := by parley_order
      have r117_2 : n > 0 := by parley_side
      have s1_2_20 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side)
      -- 1.2.21. transitivity, from 1.2.10, 1.2.18, 1.2.19, 1.2.20, 1.1
      have r122_1 : 9 * n - 3 ≠ 0 := by parley_side
      have s1_2_21 : a n - 2 / 3 < ε := by parley_order
      -- 1.2.22. inequalities
      have s1_2_22 : a n < 2 / 3 + ε := by parley_order
      -- 1.2.23. join 1.2.16, 1.2.22
      have s1_2_23 : 2 / 3 - ε < a n ∧ a n < 2 / 3 + ε := by parley_side
      -- 1.2.24. mun:abs-difference-lt x := a(n), c := 2/3, δ := ε, from 1.2.23
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := (2 / 3 : ℝ)) (δ := ε))).mpr (by parley_side)
    -- 1.3. exhibit, from 1.2
    exact ⟨N, s1_1a, s1_2⟩
  -- 2. def:tends-to L := 2/3, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (2 / 3 : ℝ)))).mpr s1

end Parley.Proofs.Hammack.RationalSequenceLimit.RationalSequenceLimit
