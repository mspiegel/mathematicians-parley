module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
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
public import Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove

/-! Written from proofs/setmm/halves-series.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.HalvesSeries.HalvesSeries

theorem halves_series :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℝ)) = 1 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on m starting at 1
  have s2 : ∀ m : ℤ, 0 < m → (∑ k ∈ Finset.Icc (1 : ℤ) m, (1 / 2 ^ k.toNat : ℚ)) = 1 - 1 / 2 ^ m.toNat := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. calculation
      have s2_1 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ k.toNat : ℚ)) = 1 - 1 / 2 ^ 1 := by
        calc (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ k.toNat : ℚ)) = 1 / 2 ^ 1 := by
              have hI : (∑ b ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ b.toNat : ℚ)) = 1 / 2 ^ 1 := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))))
              exact hI
          _ = 1 - 1 / 2 ^ 1 := by norm_num
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s2_1
    | succ m hK2 hIH =>
      -- 2.2. mun:sum-extended a := 1, n := m, from 1
      have r73_1 : m ≥ 1 := by linarith only [lt_of_lt_of_le zero_lt_one hK2]
      have s2_2 : (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), (1 / 2 ^ k.toNat : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) m, (1 / 2 ^ k.toNat : ℚ)) + 1 / 2 ^ (m + 1).toNat := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ)) (n := m) r73_1)
      -- 2.3. substitute Σ(k = 1 to m) 1/2^k = 1 − 1/2^m (IH) into line 2.2
      have s2_3 : (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), (1 / 2 ^ k.toNat : ℚ)) = 1 - 1 / 2 ^ m.toNat + 1 / 2 ^ (m + 1).toNat := by (have h := Eq.subst (motive := (fun t : ℚ => (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), (1 / 2 ^ k.toNat : ℚ)) = t + 1 / 2 ^ (m + 1).toNat)) hIH s2_2; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 2.4. mun:exponent-step a := 2
      have s2_4 : (2 ^ (m + 1).toNat : ℤ) = 2 ^ m.toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (le_of_lt (lt_of_lt_of_le zero_lt_one hK2)))
      -- 2.5. substitute 2^(m + 1) = 2^m·2 (line 2.4)
      have s2_5 : (1 / 2 ^ (m + 1).toNat : ℚ) = 1 / (2 ^ m.toNat * 2) := by
        have e_w : (2 ^ (m + 1).toNat : ℚ) = 2 ^ m.toNat * 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination (norm := parley_norm) h
        (have h := congrArg (fun t : ℚ => 1 / t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 2.6. calculation
      calc (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), (1 / 2 ^ k.toNat : ℚ)) = 1 - 1 / 2 ^ m.toNat + 1 / 2 ^ (m + 1).toNat := by exact s2_3
        _ = 1 - 1 / 2 ^ m.toNat + 1 / (2 ^ m.toNat * 2) := by (have h := congrArg (fun t : ℚ => 1 - 1 / 2 ^ m.toNat + t) s2_5; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 - 1 / (2 ^ m.toNat * 2) := by parley_ring
        _ = 1 - 1 / 2 ^ (m + 1).toNat := by (have h := congrArg (fun t : ℚ => 1 - t) s2_5.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 3. proof
  have s3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs ((∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℝ)) - 1) < ε)) := by
    intro ε
    intro hA1
    -- 3.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s3_1a, s3_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) hA1)
    -- 3.2. proof
    have s3_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs ((∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℝ)) - 1) < ε := by
      intro n hK4
      intro hA2
      -- 3.2.1. mun:power-nat a := 2, m := n
      have s3_2_1 : (0 : ℤ) < 2 ^ n.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := n) (le_of_lt hK4))
      -- 3.2.2. thm:power-of-two-above
      have s3_2_2 : n ≤ 2 ^ n.toNat := by exact (Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove.power_of_two_above (n := n) hK4)
      -- 3.2.3. transitivity, from A2, 3.2.2
      have s3_2_3 : N ≤ 2 ^ n.toNat := by exact le_trans hA2 s3_2_2
      -- 3.2.4. mun:reciprocal-order x := N, y := 2^n, from 3.2.3
      have r115_1 : N > 0 := by linarith only [s3_1a]
      have r115_2 : (2 ^ n.toNat : ℤ) > 0 := by linarith only [s3_2_1]
      have s3_2_4 : 1 / 2 ^ n.toNat ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r115_1) (y := (2 ^ n.toNat : ℚ)) (by exact_mod_cast gt_iff_lt.mp r115_2))).mp (by parley_side)
      -- 3.2.5. transitivity, from 3.2.4, 3.1
      have s3_2_5 : 1 / 2 ^ n.toNat < ε := by parley_order
      -- 3.2.6. mun:reciprocal-positive x := 2^n
      have r123_1 : (2 ^ n.toNat : ℤ) > 0 := by linarith only [s3_2_1]
      have s3_2_6 : (1 / 2 ^ n.toNat : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by exact_mod_cast gt_iff_lt.mp r123_1))
      -- 3.2.7. inequalities
      have s3_2_7 : 1 - ε < 1 - 1 / 2 ^ n.toNat := by linarith only [s3_2_5]
      -- 3.2.8. inequalities
      have s3_2_8 : (-(1 / 2 ^ n.toNat) : ℚ) < 0 := by linarith only [s3_2_6]
      -- 3.2.9. transitivity, from 3.2.8, A1
      have s3_2_9 : -(1 / 2 ^ n.toNat) < ε := by parley_order
      -- 3.2.10. inequalities
      have s3_2_10 : 1 - 1 / 2 ^ n.toNat < 1 + ε := by linarith only [s3_2_9]
      -- 3.2.11. join 3.2.7, 3.2.10
      have s3_2_11 : 1 - ε < 1 - 1 / 2 ^ n.toNat ∧ 1 - 1 / 2 ^ n.toNat < 1 + ε := by parley_side
      -- 3.2.12. mun:abs-difference-lt x := 1 − 1/2^n, c := 1, δ := ε, from 3.2.11
      have s3_2_12 : abs (1 - 1 / 2 ^ n.toNat - 1) < ε := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := (1 - 1 / 2 ^ n.toNat : ℝ)) (c := (1 : ℝ)) (δ := ε))).mpr ⟨s3_2_11.1, s3_2_11.2⟩
      -- 3.2.13. substitute
      have c1 : 1 - 1 / 2 ^ n.toNat = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℚ)) := by exact (s2 n hK4).symm
      have row1 : abs ((∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℝ)) - 1) < ε := by
        have e_w : 1 - 1 / 2 ^ n.toNat = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℝ)) := by have h := congrArg (fun x : ℚ => (x : ℝ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
        (have h := Eq.subst (motive := (fun t : ℝ => abs (t - 1) < ε)) e_w s3_2_12; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 3.3. exhibit, from 3.2
    exact ⟨N, s3_1a, s3_2⟩
  -- 4. proof
  -- what this block shows, Lean's types give
  -- 5. def:tends-to L := 1, from 3, 4
  have s5 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℝ) : ℝ)) Filter.atTop (nhds 1) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k.toNat : ℝ))) (L := (1 : ℝ)))).mpr s3
  -- 6. def:series-sum, from 1, 5
  exact (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k.toNat : ℝ))) (L := (1 : ℝ)) s5)

end Parley.Proofs.Setmm.HalvesSeries.HalvesSeries
