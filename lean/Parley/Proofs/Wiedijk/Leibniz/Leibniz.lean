module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Leibniz.IntegralBounds
public import Parley.Proofs.Wiedijk.Leibniz.SeriesRemainder

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.Leibniz

theorem leibniz :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) = Real.pi / 4 := by
  -- 1. membership
  have r738_1 : ∀ k : ℤ, 0 ≤ k → 0 < 2 * k + 1 := by intro k h_k; (exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * k) (by parley_side)))
  -- 2. thm:series-remainder
  have s2 : ∀ n : ℤ, 0 ≤ n → Real.pi / 4 - (∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) = (-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by exact Parley.Proofs.Wiedijk.Leibniz.SeriesRemainder.series_remainder
  -- 3. proof
  have s3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs ((∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) - Real.pi / 4) < ε)) := by
    intro ε
    intro hA1
    -- 3.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s3_1a, s3_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) hA1)
    -- 3.2. proof
    have s3_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs ((∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) - Real.pi / 4) < ε := by
      intro n hK2
      intro hA2
      -- 3.2.1. instantiate n := n in line 2
      have s3_2_1 : Real.pi / 4 - (∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) = (-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by exact (s2 n (le_of_lt hK2))
      -- 3.2.2. algebra, from 3.2.1
      have s3_2_2 : (∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) - Real.pi / 4 = -((-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ))) := by linear_combination (norm := parley_norm) ((-16) / ((4) * (4))) * s3_2_1
      -- 3.2.3. calculation
      have s3_2_3 : (abs (-1) : ℤ) = 1 := by
        calc (abs (-1) : ℤ) = abs 1 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := (1 : ℤ)))
          _ = 1 := by exact Parley.Items.Stdlib.Numbers.mun_abs_one
      -- 3.2.4. calculation
      have s3_2_4 : (abs ((-1) ^ (n + 1).toNat) : ℤ) = 1 := by
        calc (abs ((-1) ^ (n + 1).toNat) : ℤ) = abs (-1) ^ (n + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_abs_power (x := (-1 : ℤ)) (n := n + 1) (by parley_side))
          _ = 1 ^ (n + 1).toNat := by (have h := congrArg (fun t : ℤ => t ^ (n + 1).toNat) s3_2_3; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 1 := by (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := n + 1)); simp only [parley_zpow_toNat (n := n + 1) (h := add_nonneg (le_of_lt hK2) (by norm_num))] at h ⊢; exact_mod_cast h)
      -- 3.2.5. thm:integral-bounds n := n + 1
      have s3_2_5a : (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) ≥ 0 := by exact (Parley.Proofs.Wiedijk.Leibniz.IntegralBounds.integral_bounds (n := n + 1) (by parley_side)).2.1
      have s3_2_5b : (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) ≤ 1 / (2 * ((n : ℝ) + 1) + 1) := by
        have hI : (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) ≤ 1 / (2 * ((n : ℝ) + 1) + 1) := by parley_instance ((Parley.Proofs.Wiedijk.Leibniz.IntegralBounds.integral_bounds (n := n + 1) (by parley_side)).2.2)
        exact hI
      -- 3.2.6. def:abs x := J(n + 1), from 3.2.5
      have s3_2_6 : abs (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ))) s3_2_5a
      -- 3.2.7. algebra, from 3.2.5
      have s3_2_7 : 1 * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by parley_ring
      -- 3.2.8. calculation
      have s3_2_8 : abs ((∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) - Real.pi / 4) = (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by
        calc abs ((∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ)) - Real.pi / 4) = abs (-((-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)))) := by (have h := congrArg (fun t : ℝ => abs t) s3_2_2; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = abs ((-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ))) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := (-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ))))
          _ = abs ((-1) ^ (n + 1).toNat) * abs (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := ((-1) ^ (n + 1).toNat : ℝ)) (y := ∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)))
          _ = 1 * abs (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by
              have e_w : (abs ((-1) ^ (n + 1).toNat) : ℝ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s3_2_4; push_cast at h; linear_combination (norm := parley_norm) h
              (have h := congrArg (fun u : ℝ => u * abs (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ))) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 1 * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by (have h := congrArg (fun u : ℝ => 1 * u) s3_2_6; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by exact s3_2_7
      -- 3.2.9. inequalities, from A2, K2
      have s3_2_9 : N ≤ 2 * (n + 1) + 1 := by linarith only [hA2, hK2]
      -- 3.2.10. mun:reciprocal-order x := N, y := 2(n + 1) + 1, from 3.2.9
      have r800_1 : N > 0 := by linarith only [s3_1a]
      have r800_2 : 2 * (n + 1) + 1 > 0 := by linarith only [hK2, hK2]
      have s3_2_10 : 1 / (2 * ((n : ℚ) + 1) + 1) ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r800_1) (y := 2 * ((n : ℚ) + 1) + 1) (by exact_mod_cast gt_iff_lt.mp r800_2))).mp (by parley_side)
      -- 3.2.11. transitivity, from 3.2.8, 3.2.5, 3.2.10, 3.1
      parley_order
    -- 3.3. exhibit, from 3.2
    exact ⟨N, s3_1a, s3_2⟩
  -- 4. def:tends-to L := π/4, from 3
  have s4 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ) : ℝ)) Filter.atTop (nhds (Real.pi / 4)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ k.toNat / (2 * (k : ℝ) + 1) : ℝ))) (L := Real.pi / 4))).mpr s3
  -- 5. def:series-sum-from-zero L := π/4, from 4
  exact (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := (fun k : ℤ => (-1) ^ k.toNat / (2 * (k : ℝ) + 1))) (L := Real.pi / 4) s4)

end Parley.Proofs.Wiedijk.Leibniz.Leibniz
