module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/cauchy-schwarz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.CauchySchwarz.CauchySchwarz

theorem cauchy_schwarz (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (b : ℤ → ℝ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) ^ 2 ≤ (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) * (∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ)) := by
  -- 1. proof
  have s1 : ∀ t : ℝ, t ^ 2 * (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) + 2 * t * (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) + (∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ)) ≥ 0 := by
    intro t
    -- 1.1. mun:square-nonneg x := a(k)·t + b(k)
    have s1_1 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → (a k * t + b k) ^ 2 ≥ 0 := by intro k h_k; (exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a k * t + b k)))
    -- 1.2. mun:sum-nonneg a := 1, b := n, from 1.1
    have s1_2 : (∑ k ∈ Finset.Icc (1 : ℤ) n, ((a k * t + b k) ^ 2 : ℝ)) ≥ 0 := by exact (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := (fun k : ℤ => (a k * t + b k) ^ 2)) (a := (1 : ℤ)) (b := n) s1_1)
    -- 1.3. substitute
    have c1 : (∑ k ∈ Finset.Icc (1 : ℤ) n, ((a k * t + b k) ^ 2 : ℝ)) = t ^ 2 * (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) + 2 * t * (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) + (∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ)) := by parley_ring
    have row1 : t ^ 2 * (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) + 2 * t * (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) + (∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ)) ≥ 0 := by (have h := Eq.subst (motive := (fun u : ℝ => u ≥ 0)) c1 s1_2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 2. mun:square-nonneg x := a(k), from H2
  have s2 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → a k ^ 2 ≥ 0 := by intro k h_k; (exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a k)))
  -- 3. mun:sum-nonneg a := 1, b := n, from 2
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) ≥ 0 := by exact (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := (fun k : ℤ => a k ^ 2)) (a := (1 : ℤ)) (b := n) s2)
  -- 4. axi:trichotomy x := Σ(k = 1 to n) a(k)²
  have s4 : ((∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) < 0 ∨ (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) = 0) ∨ 0 < (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)))
  -- 5. cases, from 4
  rcases s4 with (hC1 | hC2) | hC3
  · skip
    -- 5.1. inequalities, from 3
    have s5_1 : ¬ (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) < 0 := by linarith only [s3]
    exact absurd hC1 s5_1
  · skip
    -- 5.2. mun:sum-zero-terms a := 1, b := n, from C2, 2
    have s5_2 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → a k ^ 2 = 0 := by exact (Parley.Items.Stdlib.Sums.mun_sum_zero_terms (t := (fun k : ℤ => a k ^ 2)) (a := (1 : ℤ)) (b := n) s2 hC2)
    -- 5.3. proof
    have s5_3 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → a k * b k = 0 := by
      intro k hK4
      try push_cast at hK4
      try have hK4_bounds := Finset.mem_Icc.mp hK4
      -- 5.3.1. mun:square-zero x := a(k), from H2, K4, 5.2
      have s5_3_1 : a k = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_zero (x := a k) (s5_2 k hK4))
      -- 5.3.2. algebra, from 5.3.1
      linear_combination (norm := parley_norm) (b k) * s5_3_1
    -- 5.4. calculation
    have r72_1 : 1 ≤ n := by linarith only [hH1]
    have s5_4 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) = 0 := by
      calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (0 : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => a k * b k)) (u := (fun k : ℤ => (0 : ℝ))) (a := (1 : ℤ)) (b := n) s5_3)
        _ = ((n : ℝ) - 1 + 1) * 0 := by
            have hI : (∑ k ∈ Finset.Icc (1 : ℤ) n, (0 : ℝ)) = ((n : ℝ) - 1 + 1) * 0 := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := n) r72_1 (c := (0 : ℝ))))
            exact hI
        _ = 0 := by parley_ring
    -- 5.5. algebra, from 5.4
    have s5_5 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) ^ 2 = 0 := by linear_combination (norm := parley_norm) ((∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ))) * s5_4
    -- 5.6. algebra, from C2
    have s5_6 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) * (∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ)) = 0 := by linear_combination (norm := parley_norm) ((∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ))) * hC2
    -- 5.7. transitivity, from 5.5, 5.6
    have s5_7 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) ^ 2 = (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) * (∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ)) := by exact Eq.trans s5_5 s5_6.symm
    -- 5.8. inequalities
    linarith only [s5_7]
  · skip
    set A : ℝ := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ) with hD1
    have hD1_kind : True := by parley_side
    set B : ℝ := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ) with hD2
    have hD2_kind : True := by parley_side
    set C : ℝ := ∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ) with hD3
    have hD3_kind : True := by parley_side
    -- 5.9. inequalities, from C3, D1
    have s5_9 : A > 0 := by linarith only [hC3, hD1]
    -- 5.10. instantiate t := −B/A in line 1, from D1, D2, D3
    have r112_1 : A > 0 := by linarith only [hC3, hD1]
    have s5_10 : (-(B / A)) ^ 2 * A + 2 * -(B / A) * B + C ≥ 0 := by exact (s1 (-(B / A)))
    -- 5.11. algebra
    have r116_1 : A ≠ 0 := ne_of_gt (by linarith only [s5_9])
    have s5_11 : (-(B / A)) ^ 2 * A + 2 * -(B / A) * B + C = C - B ^ 2 / A := by parley_ring
    -- 5.12. transitivity, from 5.10, 5.11
    have r120_1 : A ≠ 0 := ne_of_gt (by linarith only [s5_9])
    have s5_12 : C - B ^ 2 / A ≥ 0 := by exact LE.le.trans_eq s5_10 s5_11
    -- 5.13. inequalities
    have r124_1 : A ≠ 0 := ne_of_gt (by linarith only [s5_9])
    have s5_13 : B ^ 2 / A ≤ C := by linarith only [s5_12]
    -- 5.14. mun:multiply-le, from 5.13
    have r131_1 : A > 0 := by linarith only [hC3, hD1]
    have s5_14 : A * (B ^ 2 / A) ≤ A * C := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := B ^ 2 / A) (y := C) (c := A) s5_13 r131_1)
    -- 5.15. substitute
    have r135_1 : A ≠ 0 := ne_of_gt (by linarith only [s5_9])
    have s5_15 : B ^ 2 ≤ A * C := by
      have c1 : A * (B ^ 2 / A) = B ^ 2 := by parley_ring
      have row1 : B ^ 2 ≤ A * C := by (have h := Eq.subst (motive := (fun t : ℝ => t ≤ A * C)) c1 s5_14; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 5.16. calculation
    calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k * b k : ℝ)) ^ 2 = B ^ 2 := by simp (disch := omega) only [hD2]
      _ ≤ A * C := by exact s5_15
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) * C := by simp (disch := omega) only [hD1]
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k ^ 2 : ℝ)) * (∑ k ∈ Finset.Icc (1 : ℤ) n, (b k ^ 2 : ℝ)) := by simp (disch := omega) only [hD3]

end Parley.Proofs.Wiedijk.CauchySchwarz.CauchySchwarz
