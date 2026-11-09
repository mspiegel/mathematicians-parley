module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
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
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.AmGm.FirstTerms

/-! Written from proofs/wiedijk/am-gm.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.AmGm.AmGmPower

set_option maxHeartbeats 800000 in
theorem am_gm_power (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (hH3 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → a k ≥ 0) :
    (∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ)) ^ n.toNat := by
  -- 1. induction on j starting at 1
  have s1 : ∀ j : ℤ, 0 < j → j ≤ n → (∏ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) / (j : ℝ)) ^ j.toNat := by
    intro j h_j
    replace h_j : 1 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      intro hC1
      -- 1.1. thm:first-terms m := 1, from C1, H3
      have s1_1 : ∀ k : ℤ, k ∈ Finset.Icc 1 1 → a k ≥ 0 := by exact (Parley.Proofs.Wiedijk.AmGm.FirstTerms.first_terms (n := n) (by parley_side) (a := a) (by parley_side) (m := (1 : ℤ)) hC1).2
      -- 1.2. mun:product-single a := 1, from 1.1
      have s1_2 : (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (a k : ℝ)) = a 1 := by exact (Parley.Items.Stdlib.Sums.mun_product_single (t := a) (a := (1 : ℤ)))
      -- 1.3. mun:sum-single a := 1, from 1.1
      have s1_3 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (a k : ℝ)) = a 1 := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := a) (a := (1 : ℤ)))
      -- 1.4. transitivity, from 1.2, 1.3
      have s1_4 : (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (a k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (a k : ℝ)) := by parley_side
      -- 1.5. inequalities
      have s1_5 : (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (a k : ℝ)) / 1) ^ 1 := by parley_order
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_5
    | succ j hK1 hIH =>
      intro hC2
      -- 1.6. inequalities, from C2
      have s1_6 : j ≤ n := by parley_order
      -- 1.7. mun:modus-ponens, from IH, 1.6
      have s1_7 : (∏ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) / (j : ℝ)) ^ j.toNat := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := j ≤ n) (Q := (∏ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) / (j : ℝ)) ^ j.toNat) hIH s1_6)
      -- 1.8. thm:first-terms m := j, from H3, 1.6
      have s1_8 : ∀ k : ℤ, k ∈ Finset.Icc 1 j → a k ≥ 0 := by exact (Parley.Proofs.Wiedijk.AmGm.FirstTerms.first_terms (n := n) (by parley_side) (a := a) (by parley_side) (m := j) s1_6).2
      -- 1.9. thm:first-terms m := j + 1, from C2, H3
      have s1_9 : ∀ k : ℤ, k ∈ Finset.Icc 1 (j + 1) → a k ≥ 0 := by exact (Parley.Proofs.Wiedijk.AmGm.FirstTerms.first_terms (n := n) (by parley_side) (a := a) (by parley_side) (m := j + 1) hC2).2
      -- 1.10. def:range k := j + 1, from C2
      have s1_10 : j + 1 ∈ Finset.Icc (1 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range (k := j + 1) (n := n))).mpr (by parley_side)
      -- 1.11. instantiate k := j + 1 in H3, from 1.10
      have s1_11 : a (j + 1) ≥ 0 := by exact (hH3 (j + 1) (by parley_side))
      set x : ℝ := a (j + 1) with hD1
      have hD1_kind : True := by parley_side
      set A : ℝ := (∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) / (j : ℝ) with hD2
      have hD2_kind : True := by parley_side
      set B : ℝ := (∑ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) / ((j : ℝ) + 1) with hD3
      have hD3_kind : True := by parley_side
      -- 1.12. mun:sum-extended a := 1, n := j, from 1.9
      have r128_1 : j ≥ 1 := by parley_side
      have s1_12 : (∑ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) + a (j + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := a) (a := (1 : ℤ)) (n := j) r128_1)
      -- 1.13. algebra, from D1, D2, D3, 1.12
      have s1_13 : B * ((j : ℝ) + 1) = A * (j : ℝ) + x := by
        try simp only [hD1, hD2, hD3] at *
        try push_cast at *
        linear_combination (norm := parley_field) s1_12
      -- 1.14. mun:sum-nonneg a := 1, b := j, from 1.8
      have s1_14 : (∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) ≥ 0 := by exact (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := j) s1_8)
      -- 1.15. mun:quotient-nonneg, from D2, K1, 1.14
      have s1_15 : A ≥ 0 := by
        try simp only [hD2] at *
        try push_cast at *
        exact (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) (y := (j : ℝ)) (by parley_side) (by parley_side))
      -- 1.16. mun:sum-nonneg a := 1, b := j + 1, from 1.9
      have s1_16 : (∑ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) ≥ 0 := by exact (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := j + 1) s1_9)
      -- 1.17. mun:quotient-nonneg, from D3, 1.16
      have r146_2 : 0 < j + 1 := by parley_order
      have s1_17 : B ≥ 0 := by
        try simp only [hD3] at *
        try push_cast at *
        exact (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) (y := (j : ℝ) + 1) (by parley_side) (by parley_side))
      -- 1.18. mun:le-cases, from 1.15
      have s1_18 : 0 < A ∨ 0 = A := by exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (0 : ℝ)) (y := A))).mp s1_15
      -- 1.19. cases, from 1.18
      have s1_19 : A ^ j.toNat * x ≤ B ^ (j + 1).toNat := by
        rcases s1_18 with hC3 | hC4
        · skip
          set r : ℝ := B / A with hD4
          have hD4_kind : True := by parley_side
          -- 1.19.1. mun:quotient-nonneg, from C3, D4, 1.17
          have s1_19_1 : r ≥ 0 := by
            try simp only [hD4] at *
            try push_cast at *
            exact (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := B) (y := A) (by parley_side) (by parley_side))
          -- 1.19.2. inequalities, from 1.19.1
          have s1_19_2 : r - 1 ≥ -1 := by parley_order
          -- 1.19.3. thm:bernoulli-inequality x := r − 1, n := j + 1, from 1.19.2
          have s1_19_3 : 1 + (r - 1) * ((j : ℝ) + 1) ≤ (1 + (r - 1)) ^ (j + 1).toNat := by
            have hI : 1 + (r - 1) * ((j : ℝ) + 1) ≤ (1 + (r - 1)) ^ (j + 1).toNat := by parley_instance ((Parley.Items.Stdlib.Numbers.thm_bernoulli_inequality (x := r - 1) (n := j + 1) (by parley_side) (by parley_side)))
            exact hI
          -- 1.19.4. substitute
          have s1_19_4 : 1 + (r - 1) * ((j : ℝ) + 1) ≤ r ^ (j + 1).toNat := by
            have c1 : 1 + (r - 1) = r := by parley_ring
            have row1 : 1 + (r - 1) * ((j : ℝ) + 1) ≤ r ^ (j + 1).toNat := by parley_subst_at c1 s1_19_3
            exact row1
          -- 1.19.5. mun:power-positive, from C3
          have s1_19_5 : A ^ j.toNat > 0 := by
            have hI : 0 < A ^ j.toNat := by parley_instance ((Parley.Items.Stdlib.Numbers.mun_power_positive (a := A) (m := j) (by parley_side)))
            exact hI
          -- 1.19.6. mun:product-positive, from C3, 1.19.5
          have s1_19_6 : A ^ j.toNat * A > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := A ^ j.toNat) (y := A) (by parley_side) (by parley_side))
          -- 1.19.7. algebra, from D4
          have r185_1 : 0 ≠ A := by parley_side
          have s1_19_7 : A * r = B := by
            try simp only [hD4] at *
            try push_cast at *
            parley_ring
          -- 1.19.8. algebra, from 1.13, 1.19.7
          have s1_19_8 : (A * r - A) * ((j : ℝ) + 1) = x - A := by linear_combination (norm := parley_norm) s1_13 + ((j : ℝ) + 1) * s1_19_7
          -- 1.19.9. mun:exponent-step
          have s1_19_9 : A ^ (j + 1).toNat = A ^ j.toNat * A := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := j) (by parley_side))
          -- 1.19.10. calculation
          calc A ^ j.toNat * x = A ^ j.toNat * A * (1 + (r - 1) * ((j : ℝ) + 1)) := by linear_combination (norm := parley_norm) (-(A ^ j.toNat)) * s1_19_8
            _ ≤ A ^ j.toNat * A * r ^ (j + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := 1 + (r - 1) * ((j : ℝ) + 1)) (y := r ^ (j + 1).toNat) (c := A ^ j.toNat * A) (by parley_side) (by parley_side))
            _ = A ^ (j + 1).toNat * r ^ (j + 1).toNat := by parley_subst s1_19_9
            _ = (A * r) ^ (j + 1).toNat := by linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := A) (b := r) (n := j + 1) (by parley_side)).symm
            _ = B ^ (j + 1).toNat := by parley_subst s1_19_7
        · skip
          -- 1.19.11. substitute 0 = A (C4)
          have s1_19_11 : A ^ j.toNat * x = 0 ^ j.toNat * x := by parley_subst hC4
          -- 1.19.12. mun:zero-power n := j
          have s1_19_12 : (0 ^ j.toNat : ℤ) = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_zero_power (n := j) (by parley_side))
          -- 1.19.13. algebra, from 1.19.11, 1.19.12
          have s1_19_13 : A ^ j.toNat * x = 0 := by
            have s1_19_12_w : (0 ^ j.toNat : ℝ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1_19_12; push_cast at h; linear_combination (norm := parley_norm) h
            linear_combination (norm := parley_norm) s1_19_11 + (x) * s1_19_12_w
          -- 1.19.14. mun:power-nonneg, from 1.17
          have s1_19_14 : B ^ (j + 1).toNat ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := B) (m := j + 1) (by parley_side) (by parley_side))
          -- 1.19.15. transitivity, from 1.19.13, 1.19.14
          parley_order
      -- 1.20. calculation
      have r222_1 : j ≥ 1 := by parley_side
      have s1_20 : (∏ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) / ((j : ℝ) + 1)) ^ (j + 1).toNat := by
        calc (∏ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) = (∏ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) * a (j + 1) := by exact (Parley.Items.Stdlib.Sums.mun_product_extended (t := a) (a := (1 : ℤ)) (n := j) r222_1)
          _ = (∏ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) * x := by simp (disch := omega) only [hD1]
          _ ≤ A ^ j.toNat * x := by
              try simp only [hD1, hD2] at *
              try push_cast at *
              exact (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := ∏ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) (y := ((∑ k ∈ Finset.Icc (1 : ℤ) j, (a k : ℝ)) / (j : ℝ)) ^ j.toNat) (c := a (j + 1)) (by parley_side) (by parley_side))
          _ ≤ B ^ (j + 1).toNat := by exact s1_19
          _ = ((∑ k ∈ Finset.Icc (1 : ℤ) (j + 1), (a k : ℝ)) / ((j : ℝ) + 1)) ^ (j + 1).toNat := by simp (disch := omega) only [hD3]
      first | exact_mod_cast s1_20 | (have h := s1_20; push_cast at h ⊢; exact h) | simpa using s1_20
  -- 2. instantiate j := n in line 1
  have s2 : n ≤ n → (∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ)) ^ n.toNat := by exact (s1 n (by parley_side))
  -- 3. inequalities
  have s3 : n ≤ n := by parley_order
  -- 4. mun:modus-ponens, from 2, 3
  exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := n ≤ n) (Q := (∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ≤ ((∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ)) ^ n.toNat) s2 s3)

end Parley.Proofs.Wiedijk.AmGm.AmGmPower
