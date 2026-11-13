module

public import AlgebraTactics
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
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/rational-function-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalFunctionLimit.RationalFunctionLimit

theorem rational_function_limit (a : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → a n = (5 * (n : ℝ) ^ 2 + (n : ℝ) + 1) / (4 * (n : ℝ) ^ 2 + 2)) :
    Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds (5 / 4)) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 5 / 4) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) hA1)
    -- 1.2. proof
    have s1_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs (a n - 5 / 4) < ε := by
      intro n hK2
      intro hA2
      -- 1.2.1. inequalities, from K2
      have s1_2_1 : n > 0 := by linarith only [hK2]
      -- 1.2.2. inequalities, from K2
      have s1_2_2 : n ≥ 1 := by linarith only [hK2]
      -- 1.2.3. mun:square-positive x := n
      have r40_1 : n ≠ 0 := ne_of_gt (by linarith only [s1_2_1])
      have s1_2_3 : n ^ 2 > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_positive (x := n) r40_1)
      -- 1.2.4. inequalities
      have s1_2_4 : 4 * n ^ 2 > 0 := by linarith only [s1_2_3]
      -- 1.2.5. inequalities, from 1.2.4
      have s1_2_5 : 4 * n ^ 2 + 2 > 0 := by linarith only [s1_2_4]
      -- 1.2.6. inequalities
      have s1_2_6 : 8 * n ^ 2 + 4 > 0 := by linarith only [s1_2_5]
      -- 1.2.7. mun:product-positive x := n, y := 8n² + 4, from 1.2.1, 1.2.6
      have s1_2_7 : n * (8 * n ^ 2 + 4) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := n) (y := 8 * n ^ 2 + 4) s1_2_1 s1_2_6)
      -- 1.2.8. algebra, from H2
      have s1_2_8 : a n - 5 / 4 = (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) := by linear_combination (norm := parley_field) ((4) / ((4))) * (hH2 n hK2)
      -- 1.2.9. algebra
      have s1_2_9 : 1 / (n : ℚ) - (2 * (n : ℚ) - 3) / (8 * (n : ℚ) ^ 2 + 4) = (6 * (n : ℚ) ^ 2 + 3 * (n : ℚ) + 4) / ((n : ℚ) * (8 * (n : ℚ) ^ 2 + 4)) := by parley_ring
      -- 1.2.10. inequalities
      have s1_2_10 : 6 * n ^ 2 > 0 := by linarith only [s1_2_3]
      -- 1.2.11. inequalities
      have s1_2_11 : 3 * n > 0 := by linarith only [s1_2_1]
      -- 1.2.12. inequalities, from 1.2.10, 1.2.11
      have s1_2_12 : 6 * n ^ 2 + 3 * n + 4 > 0 := by linarith only [s1_2_10, s1_2_11]
      -- 1.2.13. mun:quotient-positive x := 6n² + 3n + 4, y := n·(8n² + 4), from 1.2.7, 1.2.12
      have s1_2_13 : (6 * (n : ℚ) ^ 2 + 3 * (n : ℚ) + 4) / ((n : ℚ) * (8 * (n : ℚ) ^ 2 + 4)) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 6 * (n : ℚ) ^ 2 + 3 * (n : ℚ) + 4) (y := (n : ℚ) * (8 * (n : ℚ) ^ 2 + 4)) (by exact_mod_cast gt_iff_lt.mp s1_2_12) (by exact_mod_cast gt_iff_lt.mp s1_2_7))
      -- 1.2.14. transitivity, from 1.2.13, 1.2.9
      have s1_2_14 : 0 < 1 / (n : ℚ) - (2 * (n : ℚ) - 3) / (8 * (n : ℚ) ^ 2 + 4) := by exact LT.lt.trans_eq s1_2_13 s1_2_9.symm
      -- 1.2.15. inequalities
      have s1_2_15 : (2 * (n : ℚ) - 3) / (8 * (n : ℚ) ^ 2 + 4) < 1 / (n : ℚ) := by linarith only [s1_2_14]
      -- 1.2.16. algebra
      have s1_2_16 : 1 / (n : ℚ) + (2 * (n : ℚ) - 3) / (8 * (n : ℚ) ^ 2 + 4) = (10 * (n : ℚ) ^ 2 - 3 * (n : ℚ) + 4) / ((n : ℚ) * (8 * (n : ℚ) ^ 2 + 4)) := by parley_ring
      -- 1.2.17. mun:multiply-le x := 1, y := n, c := n, from 1.2.2
      have r95_1 : n > 0 := by parley_side
      have s1_2_17 : n * 1 ≤ n * n := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) s1_2_2 r95_1)
      -- 1.2.18. algebra
      have s1_2_18 : n * n = n ^ 2 := by parley_ring
      -- 1.2.19. transitivity, from 1.2.17, 1.2.18
      have s1_2_19 : n ≤ n ^ 2 := by linarith only [s1_2_17, s1_2_18]
      -- 1.2.20. inequalities
      have s1_2_20 : 7 * n ^ 2 ≤ 10 * n ^ 2 - 3 * n := by linarith only [s1_2_19]
      -- 1.2.21. inequalities
      have s1_2_21 : 7 * n ^ 2 > 0 := by linarith only [s1_2_3]
      -- 1.2.22. transitivity, from 1.2.21, 1.2.20
      have s1_2_22 : 0 < 10 * n ^ 2 - 3 * n := by exact lt_of_lt_of_le s1_2_21 s1_2_20
      -- 1.2.23. mun:quotient-positive x := 10n² − 3n + 4, y := n·(8n² + 4), from 1.2.7
      have r122_1 : 10 * n ^ 2 - 3 * n + 4 > 0 := by linarith only [s1_2_22]
      have s1_2_23 : (10 * (n : ℚ) ^ 2 - 3 * (n : ℚ) + 4) / ((n : ℚ) * (8 * (n : ℚ) ^ 2 + 4)) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 10 * (n : ℚ) ^ 2 - 3 * (n : ℚ) + 4) (y := (n : ℚ) * (8 * (n : ℚ) ^ 2 + 4)) (by exact_mod_cast gt_iff_lt.mp r122_1) (by exact_mod_cast gt_iff_lt.mp s1_2_7))
      -- 1.2.24. transitivity, from 1.2.23, 1.2.16
      have s1_2_24 : 0 < 1 / (n : ℚ) + (2 * (n : ℚ) - 3) / (8 * (n : ℚ) ^ 2 + 4) := by exact LT.lt.trans_eq s1_2_23 s1_2_16.symm
      -- 1.2.25. inequalities
      have s1_2_25 : -(1 / (n : ℚ)) < (2 * (n : ℚ) - 3) / (8 * (n : ℚ) ^ 2 + 4) := by linarith only [s1_2_24]
      -- 1.2.26. mun:reciprocal-order x := N, y := n, from A2
      have r135_1 : N > 0 := by linarith only [s1_1a]
      have r135_2 : n > 0 := by parley_side
      have s1_2_26 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r135_1) (y := (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r135_2))).mp (by exact_mod_cast ge_iff_le.mp hA2)
      -- 1.2.27. transitivity, from 1.2.26, 1.1
      have s1_2_27 : 1 / (n : ℝ) < ε := by exact lt_of_le_of_lt (show 1 / (n : ℝ) ≤ 1 / (N : ℝ) by have h := (Rat.cast_le (K := ℝ)).mpr s1_2_26; simp only [Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; exact h) s1_1b
      -- 1.2.28. transitivity, from 1.2.8, 1.2.15, 1.2.27
      have s1_2_28 : a n - 5 / 4 < ε := by exact lt_trans (Eq.trans_lt s1_2_8 (show (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) < 1 / (n : ℝ) by have h := (Rat.cast_lt (K := ℝ)).mpr s1_2_15; simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h)) s1_2_27
      -- 1.2.29. inequalities
      have s1_2_29 : a n < 5 / 4 + ε := by linarith only [s1_2_28]
      -- 1.2.30. inequalities
      have s1_2_30 : -ε < -(1 / (n : ℝ)) := by linarith only [s1_2_27]
      -- 1.2.31. transitivity, from 1.2.30, 1.2.25, 1.2.8
      have s1_2_31 : -ε < a n - 5 / 4 := by exact LT.lt.trans_eq (lt_trans s1_2_30 (show -(1 / (n : ℝ)) < (2 * (n : ℝ) - 3) / (8 * (n : ℝ) ^ 2 + 4) by have h := (Rat.cast_lt (K := ℝ)).mpr s1_2_25; simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h)) s1_2_8.symm
      -- 1.2.32. inequalities
      have s1_2_32 : 5 / 4 - ε < a n := by linarith only [s1_2_31]
      -- 1.2.33. join 1.2.32, 1.2.29
      have s1_2_33 : 5 / 4 - ε < a n ∧ a n < 5 / 4 + ε := ⟨s1_2_32, s1_2_29⟩
      -- 1.2.34. mun:abs-difference-lt x := a(n), c := 5/4, δ := ε, from 1.2.33
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := (5 / 4 : ℝ)) (δ := ε))).mpr ⟨s1_2_33.1, s1_2_33.2⟩
    -- 1.3. exhibit, from 1.2
    exact ⟨N, s1_1a, s1_2⟩
  -- 2. def:tends-to L := 5/4, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (5 / 4 : ℝ)))).mpr s1

end Parley.Proofs.Hammack.RationalFunctionLimit.RationalFunctionLimit
