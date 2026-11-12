module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
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
public import Parley.Proofs.Setmm.LimitLemmas.ScaledSmall

/-! Written from proofs/setmm/a-over-n-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AOverNLimit.AOverNTendsToZero

theorem a_over_n_tends_to_zero (A : ℝ) :
    Filter.Tendsto (fun n : ℤ => (A / (n : ℝ) : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. mun:abs-nonneg x := A
  have s1 : abs A ≥ 0 := by
    have hI : 0 ≤ abs A := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (A : ℂ))))
    exact hI
  -- 2. inequalities, from 1
  have s2 : abs A + 1 > 0 := by linarith only [s1]
  -- 3. inequalities
  have s3 : 2 * (abs A + 1) > 0 := by linarith only [s2]
  -- 4. proof
  -- what this block shows, Lean's types give
  -- 5. proof
  have s5 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (A / (n : ℝ)) < ε)) := by
    intro ε
    intro hA1
    -- 5.1. membership
    have r42_1 : 2 * (abs A + 1) ≠ 0 := ne_of_gt (by linarith only [s3])
    -- 5.2. mun:quotient-positive x := ε, y := 2·(|A| + 1), from A1, 3
    have s5_2 : ε / (2 * (abs A + 1)) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs A + 1)) hA1 s3)
    -- 5.3. obtain N: thm:archimedean x := ε/(2·(|A| + 1)), from 5.1, 5.2
    obtain ⟨N, s5_3a, s5_3b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε / (2 * (abs A + 1))) s5_2)
    -- 5.4. proof
    have s5_4 : ∀ n : ℤ, 0 < n → n ≥ N → abs (A / (n : ℝ)) < ε := by
      intro n hK3
      intro hA2
      -- 5.4.1. mun:reciprocal-order x := N, y := n, from A2
      have r57_1 : N > 0 := by linarith only [s5_3a]
      have r57_2 : n > 0 := by linarith only [hK3]
      have s5_4_1 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r57_1) (y := (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r57_2))).mp (by parley_side)
      -- 5.4.2. transitivity, from 5.4.1, 5.3
      have r62_1 : 2 * (abs A + 1) ≠ 0 := ne_of_gt (by linarith only [s3])
      have s5_4_2 : 1 / (n : ℝ) < ε / (2 * (abs A + 1)) := by parley_order
      -- 5.4.3. mun:reciprocal-positive x := n
      have r66_1 : n > 0 := by linarith only [hK3]
      have s5_4_3 : 1 / (n : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r66_1))
      -- 5.4.4. inequalities
      have s5_4_4 : 1 / (n : ℚ) ≥ 0 := by linarith only [s5_4_3]
      -- 5.4.5. substitute
      have s5_4_5 : abs (1 / (n : ℝ)) < ε / (2 * (abs A + 1)) := by
        have c1 : 1 / (n : ℚ) = abs (1 / (n : ℚ)) := by exact ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) s5_4_4).symm
        have row1 : abs (1 / (n : ℝ)) < ε / (2 * (abs A + 1)) := by
          have e_w : 1 / (n : ℝ) = abs (1 / (n : ℝ)) := by have h := congrArg (fun x : ℚ => (x : ℝ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := Eq.subst (motive := (fun t : ℝ => t < ε / (2 * (abs A + 1)))) e_w s5_4_2; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 5.4.6. thm:scaled-small C := A, u := 1/n, from A1, 5.4.5
      have s5_4_6 : abs (A * (1 / (n : ℝ))) < ε := by exact (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := A) (u := 1 / (n : ℝ)) (ε := ε) (by parley_side) s5_4_5)
      -- 5.4.7. substitute
      have c1 : A * (1 / (n : ℝ)) = A / (n : ℝ) := by parley_ring
      have row1 : abs (A / (n : ℝ)) < ε := by (have h := Eq.subst (motive := (fun t : ℝ => abs t < ε)) c1 s5_4_6; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 5.5. exhibit, from 5.4
    exact ⟨N, s5_3a, s5_4⟩
  -- 6. def:tends-to L := 0, from 4, 5
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => A / (n : ℝ))) (L := (0 : ℝ)))).mpr (by simpa only [sub_zero] using s5)

end Parley.Proofs.Setmm.AOverNLimit.AOverNTendsToZero
