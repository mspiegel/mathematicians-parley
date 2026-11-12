module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/triangular-reciprocals.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.TriangularReciprocals.TriangularReciprocals

theorem triangular_reciprocals :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) = 2 := by
  -- 1. proof
  have s1 : ∀ k : ℤ, 0 < k → 1 / ((k : ℚ) * ((k : ℚ) + 1) / 2) = 2 / (k : ℚ) - 2 / ((k : ℚ) + 1) := by
    intro k hK1
    -- 1.1. calculation
    calc 1 / ((k : ℚ) * ((k : ℚ) + 1) / 2) = 1 / ((k : ℚ) * ((k : ℚ) + 1) / 2) := by parley_side
      _ = 2 / (k : ℚ) - 2 / ((k : ℚ) + 1) := by parley_ring
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. proof
  -- what this block shows, Lean's types give
  -- 4. proof
  -- what this block shows, Lean's types give
  -- 5. proof
  have s5 : ∀ n : ℤ, 0 < n → (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℚ) * ((k : ℚ) + 1) / 2) : ℚ)) = 2 - 2 / ((n : ℚ) + 1) := by
    intro n hK5
    -- 5.1. calculation
    have r55_1 : n + 1 ≥ 1 := by linarith only [hK5]
    calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℚ) * ((k : ℚ) + 1) / 2) : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (2 / (k : ℚ) - 2 / ((k : ℚ) + 1) : ℚ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 1 / ((k : ℚ) * ((k : ℚ) + 1) / 2))) (u := (fun k : ℤ => 2 / (k : ℚ) - 2 / ((k : ℚ) + 1))) (a := (1 : ℤ)) (b := n) (by parley_side))
      _ = 2 - 2 / ((n : ℚ) + 1) := by (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes (t := (fun k : ℤ => 2 / (k : ℚ))) (a := (1 : ℤ)) (b := n) r55_1); simp only [Int.cast_one, div_one] at h ⊢; exact_mod_cast h)
  -- 6. proof
  have s6 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs ((∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) - 2) < ε)) := by
    intro ε
    intro hA1
    -- 6.1. obtain N: thm:archimedean x := ε/2
    have r67_1 : ε / 2 > 0 := by linarith only [hA1]
    obtain ⟨N, s6_1a, s6_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε / 2) r67_1)
    -- 6.2. proof
    have s6_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs ((∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) - 2) < ε := by
      intro n hK7
      intro hA2
      -- 6.2.1. inequalities, from A2
      have s6_2_1 : N ≤ n + 1 := by linarith only [hA2]
      -- 6.2.2. mun:reciprocal-order x := N, y := n + 1, from 6.2.1
      have r79_1 : N > 0 := by linarith only [s6_1a]
      have r79_2 : n + 1 > 0 := by linarith only [hK7]
      have s6_2_2 : 1 / ((n : ℚ) + 1) ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r79_1) (y := (n : ℚ) + 1) (by exact_mod_cast gt_iff_lt.mp r79_2))).mp (by parley_side)
      -- 6.2.3. mun:reciprocal-positive x := n + 1
      have r84_1 : n + 1 > 0 := by linarith only [hK7]
      have s6_2_3 : 1 / ((n : ℚ) + 1) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ) + 1) (by exact_mod_cast gt_iff_lt.mp r84_1))
      -- 6.2.4. transitivity, from 6.2.2, 6.1
      have s6_2_4 : 1 / ((n : ℝ) + 1) < ε / 2 := by exact lt_of_le_of_lt (show 1 / ((n : ℝ) + 1) ≤ 1 / (N : ℝ) by have h := (Rat.cast_le (K := ℝ)).mpr s6_2_2; simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; exact h) s6_1b
      -- 6.2.5. inequalities
      have s6_2_5 : 2 - ε < 2 - 2 / ((n : ℝ) + 1) := by linarith only [s6_2_4, div_eq_mul_one_div (2 : ℝ) ((n : ℝ) + 1)]
      -- 6.2.6. transitivity, from 6.2.5, 5
      have s6_2_6 : 2 - ε < (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) := by exact LT.lt.trans_eq s6_2_5 (show (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) = 2 - 2 / ((n : ℝ) + 1) by have h := (Rat.cast_inj (α := ℝ)).mpr (s5 n hK7); simp only [Rat.cast_sum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h).symm
      -- 6.2.7. inequalities
      have s6_2_7 : 2 - 2 / ((n : ℚ) + 1) < 2 := by linarith only [s6_2_3, div_eq_mul_one_div (2 : ℚ) ((n : ℚ) + 1)]
      -- 6.2.8. inequalities, from A1, 6.2.7
      have s6_2_8 : 2 - 2 / ((n : ℝ) + 1) < 2 + ε := by linarith only [hA1, (show 2 - 2 / ((n : ℝ) + 1) < 2 by have h := (Rat.cast_lt (K := ℝ)).mpr s6_2_7; simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h)]
      -- 6.2.9. transitivity, from 5, 6.2.8
      have s6_2_9 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) < 2 + ε := by exact Eq.trans_lt (show (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) = 2 - 2 / ((n : ℝ) + 1) by have h := (Rat.cast_inj (α := ℝ)).mpr (s5 n hK7); simp only [Rat.cast_sum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h) s6_2_8
      -- 6.2.10. mun:abs-difference-lt x := Σ(k = 1 to n) 1/T(k), c := 2, δ := ε, from 6.2.6, 6.2.9
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ)) (c := (2 : ℝ)) (δ := ε))).mpr ⟨s6_2_6, s6_2_9⟩
    -- 6.3. exhibit, from 6.2
    exact ⟨N, s6_1a, s6_2⟩
  -- 7. def:tends-to L := 2, from 6
  have s7 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ) : ℝ)) Filter.atTop (nhds 2) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1) / 2) : ℝ))) (L := (2 : ℝ)))).mpr s6
  -- 8. def:series-sum L := 2, from 7
  exact (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1) / 2))) (L := (2 : ℝ)) s7)

end Parley.Proofs.Wiedijk.TriangularReciprocals.TriangularReciprocals
