module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseComplement

theorem choose_complement (N : ℤ) (hH1 : 0 ≤ N) (K : ℤ) :
    (LeanBridges.Counting.choose N K : ℤ) = (LeanBridges.Counting.choose N (N - K) : ℤ) := by
  -- 1. axi:excluded-middle P := K ∈ {0, …, N}
  have s1 : K ∈ Finset.Icc (0 : ℤ) N ∨ ¬ K ∈ Finset.Icc (0 : ℤ) N := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := K ∈ Finset.Icc (0 : ℤ) N))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:range-nat0 n := N, from C1
    have s2_1 : 0 ≤ K := by exact (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := N) (k := K) hC1)
    -- 2.2. mun:range-difference a := 0, n := N, from C1
    have s2_2 : 0 ≤ N - K := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := N) (k := K) hC1)
    -- 2.3. inequalities, from 2.1, 2.2
    have s2_3a : 0 ≤ N - K := by parley_order
    have s2_3b : N - K ≤ N := by parley_order
    -- 2.4. def:range-between k := N − K, a := 0, b := N, from 2.3
    have s2_4 : N - K ∈ Finset.Icc (0 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mpr ⟨s2_3a, s2_3b⟩
    -- 2.5. algebra
    have s2_5 : N - (N - K) = K := by parley_ring
    -- 2.6. substitute N − (N − K) = K (line 2.5)
    have s2_6 : (LeanBridges.Counting.factorial (N - (N - K)) : ℤ) = (LeanBridges.Counting.factorial K : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ)) s2_5; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.7. mun:factorial-nat n := N − K, from 2.2
    have s2_7 : 0 < (LeanBridges.Counting.factorial (N - K) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N - K) s2_2)
    -- 2.8. mun:factorial-nat n := K, from 2.1
    have s2_8 : 0 < (LeanBridges.Counting.factorial K : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := K) s2_1)
    -- 2.9. calculation
    try qify
    calc (LeanBridges.Counting.choose N K : ℚ) = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - K) : ℚ) * (LeanBridges.Counting.factorial K : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := N) hH1 (k := K)) hC1
      _ = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial K : ℚ) * (LeanBridges.Counting.factorial (N - K) : ℚ)) := by parley_ring
      _ = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - (N - K)) : ℚ) * (LeanBridges.Counting.factorial (N - K) : ℚ)) := by
          have e_w : (LeanBridges.Counting.factorial K : ℚ) = (LeanBridges.Counting.factorial (N - (N - K)) : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_6.symm; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun t : ℚ => (LeanBridges.Counting.factorial N : ℚ) / (t * (LeanBridges.Counting.factorial (N - K) : ℚ))) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.choose N (N - K) : ℚ) := by exact ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) hH1 (k := N - K)) s2_4).symm
  · skip
    -- 2.10. contradiction
    have s2_10 : ¬ N - K ∈ Finset.Icc (0 : ℤ) N := by
      intro hS
      -- 2.10.1. def:range-between k := N − K, a := 0, b := N, from S
      have s2_10_1a : 0 ≤ N - K := by exact (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp hS).1
      have s2_10_1b : N - K ≤ N := by exact (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp hS).2
      -- 2.10.2. inequalities
      have s2_10_2 : K ≥ 0 := by parley_order
      -- 2.10.3. inequalities
      have s2_10_3 : K ≤ N := by parley_order
      -- 2.10.4. def:range-between k := K, a := 0, b := N, from 2.10.2, 2.10.3
      have s2_10_4 : K ∈ Finset.Icc (0 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range_between (k := K) (a := (0 : ℤ)) (b := N))).mpr ⟨s2_10_2, s2_10_3⟩
      -- 2.10.5. restate C2
      have s2_10_5 : ¬ K ∈ Finset.Icc (0 : ℤ) N := by exact hC2
      exact s2_10_5 s2_10_4
    -- 2.11. calculation
    calc (LeanBridges.Counting.choose N K : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) hH1 (k := K) hC2)
      _ = (LeanBridges.Counting.choose N (N - K) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) hH1 (k := N - K) s2_10).symm

end Parley.Proofs.Setmm.BinomialBasics.ChooseComplement
