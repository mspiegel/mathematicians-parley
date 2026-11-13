module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/rational-sequence-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSequenceLimit.RationalSequenceLimit

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
      have s1_2_1 : n ≥ 1 := by linarith only [hK2]
      -- 1.2.2. inequalities, from K2
      have s1_2_2 : n > 0 := by linarith only [hK2]
      -- 1.2.3. inequalities
      have s1_2_3 : 3 * n - 1 ≥ 2 := by linarith only [s1_2_1]
      -- 1.2.4. inequalities, from 1.2.3
      have s1_2_4 : 3 * n - 1 > 0 := by linarith only [s1_2_3]
      -- 1.2.5. inequalities
      have s1_2_5 : 9 * n - 3 ≥ 5 * n + 1 := by linarith only [s1_2_1]
      -- 1.2.6. inequalities, from 1.2.5
      have s1_2_6 : 5 * n ≤ 9 * n - 3 := by linarith only [s1_2_5]
      -- 1.2.7. inequalities
      have s1_2_7 : 5 * n > 0 := by linarith only [s1_2_2]
      -- 1.2.8. transitivity, from 1.2.7, 1.2.6
      have s1_2_8 : 9 * n - 3 > 0 := by exact lt_of_lt_of_le s1_2_7 s1_2_6
      -- 1.2.9. inequalities
      have s1_2_9 : 9 * n - 3 ≠ 0 := ne_of_gt (by linarith only [s1_2_8])
      -- 1.2.10. algebra, from H2
      have r68_1 : 3 * n - 1 ≠ 0 := ne_of_gt (by linarith only [s1_2_4])
      have r68_2 : 9 * n - 3 ≠ 0 := by exact s1_2_9
      have s1_2_10 : a n - 2 / 3 = 5 * (1 / (9 * (n : ℝ) - 3)) := by linear_combination (norm := parley_field) ((3) / ((3))) * (hH2 n hK2)
      -- 1.2.11. mun:reciprocal-positive x := 9n − 3, from 1.2.8
      have s1_2_11 : 1 / (9 * (n : ℚ) - 3) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := 9 * (n : ℚ) - 3) (by exact_mod_cast gt_iff_lt.mp s1_2_8))
      -- 1.2.12. inequalities
      have r76_1 : 9 * n - 3 ≠ 0 := by exact s1_2_9
      have s1_2_12 : 5 * (1 / (9 * (n : ℚ) - 3)) > 0 := by linarith only [s1_2_11]
      -- 1.2.13. transitivity, from 1.2.12, 1.2.10
      have r82_1 : 9 * n - 3 ≠ 0 := by exact s1_2_9
      have s1_2_13 : a n - 2 / 3 > 0 := by exact LT.lt.trans_eq (show 5 * (1 / (9 * (n : ℝ) - 3)) > 0 by have h := (Rat.cast_lt (K := ℝ)).mpr s1_2_12; simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h) s1_2_10.symm
      -- 1.2.14. inequalities
      have s1_2_14 : a n > 2 / 3 := by linarith only [s1_2_13]
      -- 1.2.15. inequalities
      have s1_2_15 : 2 / 3 - ε < 2 / 3 := by linarith only [hA1]
      -- 1.2.16. transitivity, from 1.2.15, 1.2.14
      have s1_2_16 : 2 / 3 - ε < a n := by exact lt_trans s1_2_15 s1_2_14
      -- 1.2.17. mun:reciprocal-order x := 5n, y := 9n − 3, from 1.2.6
      have r103_1 : 5 * n > 0 := by exact s1_2_7
      have r103_2 : 9 * n - 3 > 0 := by exact s1_2_8
      have s1_2_17 : 1 / (9 * (n : ℚ) - 3) ≤ 1 / (5 * (n : ℚ)) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 5 * (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r103_1) (y := 9 * (n : ℚ) - 3) (by exact_mod_cast gt_iff_lt.mp r103_2))).mp (by exact_mod_cast s1_2_6)
      -- 1.2.18. inequalities
      have r108_1 : 9 * n - 3 ≠ 0 := by exact s1_2_9
      have s1_2_18 : 5 * (1 / (9 * (n : ℚ) - 3)) ≤ 5 * (1 / (5 * (n : ℚ))) := by linarith only [s1_2_17]
      -- 1.2.19. algebra
      have s1_2_19 : 5 * (1 / (5 * (n : ℚ))) = 1 / (n : ℚ) := by parley_ring
      -- 1.2.20. mun:reciprocal-order x := N, y := n, from A2
      have r117_1 : N > 0 := by linarith only [s1_1a]
      have r117_2 : n > 0 := by exact s1_2_2
      have s1_2_20 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r117_1) (y := (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r117_2))).mp (by exact_mod_cast ge_iff_le.mp hA2)
      -- 1.2.21. transitivity, from 1.2.10, 1.2.18, 1.2.19, 1.2.20, 1.1
      have r122_1 : 9 * n - 3 ≠ 0 := by exact s1_2_9
      have s1_2_21 : a n - 2 / 3 < ε := by exact lt_of_le_of_lt (le_trans (LE.le.trans_eq (Eq.trans_le s1_2_10 (show 5 * (1 / (9 * (n : ℝ) - 3)) ≤ 5 * (1 / (5 * (n : ℝ))) by have h := (Rat.cast_le (K := ℝ)).mpr s1_2_18; simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h)) (show 5 * (1 / (5 * (n : ℝ))) = 1 / (n : ℝ) by have h := (Rat.cast_inj (α := ℝ)).mpr s1_2_19; simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h)) (show 1 / (n : ℝ) ≤ 1 / (N : ℝ) by have h := (Rat.cast_le (K := ℝ)).mpr s1_2_20; simp only [Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; exact h)) s1_1b
      -- 1.2.22. inequalities
      have s1_2_22 : a n < 2 / 3 + ε := by linarith only [s1_2_21]
      -- 1.2.23. join 1.2.16, 1.2.22
      have s1_2_23 : 2 / 3 - ε < a n ∧ a n < 2 / 3 + ε := ⟨s1_2_16, s1_2_22⟩
      -- 1.2.24. mun:abs-difference-lt x := a(n), c := 2/3, δ := ε, from 1.2.23
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := (2 / 3 : ℝ)) (δ := ε))).mpr ⟨s1_2_23.1, s1_2_23.2⟩
    -- 1.3. exhibit, from 1.2
    exact ⟨N, s1_1a, s1_2⟩
  -- 2. def:tends-to L := 2/3, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (2 / 3 : ℝ)))).mpr s1

end Parley.Proofs.Hammack.RationalSequenceLimit.RationalSequenceLimit
