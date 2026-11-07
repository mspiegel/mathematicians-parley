module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseComplement

set_option maxHeartbeats 400000 in
theorem choose_complement (N : ℤ) (hH1 : 0 ≤ N) (K : ℤ) :
    (LeanBridges.Counting.choose N K : ℤ) = (LeanBridges.Counting.choose N (N - K) : ℤ) := by
  -- 1. axi:excluded-middle P := K ∈ {0, …, N}
  have s1 : K ∈ Finset.Icc (0 : ℤ) N ∨ ¬ K ∈ Finset.Icc (0 : ℤ) N := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := K ∈ Finset.Icc (0 : ℤ) N))
  -- 2. cases, from 1
  have s2 : (LeanBridges.Counting.choose N K : ℤ) = (LeanBridges.Counting.choose N (N - K) : ℤ) := by
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
      have s2_4 : N - K ∈ Finset.Icc (0 : ℤ) N := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mpr (by parley_side); parley_side)
      -- 2.5. algebra
      have s2_5 : N - (N - K) = K := by parley_ring
      -- 2.6. substitute N − (N − K) = K (line 2.5)
      have s2_6 : (LeanBridges.Counting.factorial (N - (N - K)) : ℤ) = (LeanBridges.Counting.factorial K : ℤ) := by parley_subst s2_5
      -- 2.7. mun:factorial-nat n := N − K, from 2.2
      have s2_7 : 0 < (LeanBridges.Counting.factorial (N - K) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N - K) (by parley_side))
      -- 2.8. mun:factorial-nat n := K, from 2.1
      have s2_8 : 0 < (LeanBridges.Counting.factorial K : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := K) (by parley_side))
      -- 2.9. calculation
      have s2_9 : (LeanBridges.Counting.choose N K : ℤ) = (LeanBridges.Counting.choose N (N - K) : ℤ) := by
        try qify
        calc (LeanBridges.Counting.choose N K : ℚ) = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - K) : ℚ) * (LeanBridges.Counting.factorial K : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := K)) (by parley_side); parley_side)
          _ = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial K : ℚ) * (LeanBridges.Counting.factorial (N - K) : ℚ)) := by parley_ring
          _ = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - (N - K)) : ℚ) * (LeanBridges.Counting.factorial (N - K) : ℚ)) := by
              have s2_6_w : (LeanBridges.Counting.factorial (N - (N - K)) : ℚ) = (LeanBridges.Counting.factorial K : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_6; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_6_w | parley_subst s2_6
          _ = (LeanBridges.Counting.choose N (N - K) : ℚ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N - K)) (by parley_side); parley_side)
      all_goals parley_side
    · skip
      -- 2.10. contradiction
      have s2_10 : ¬ N - K ∈ Finset.Icc (0 : ℤ) N := by
        by_contra hc_hS
        have hS : N - K ∈ Finset.Icc (0 : ℤ) N := by parley_suppose hc_hS
        -- 2.10.1. def:range-between k := N − K, a := 0, b := N, from S
        have s2_10_1a : 0 ≤ N - K := by first | linarith [(((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).1] | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).1; parley_side)
        have s2_10_1b : N - K ≤ N := by first | linarith [(((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).2] | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sums.def_range_between (k := N - K) (a := (0 : ℤ)) (b := N))).mp (by parley_side)).2; parley_side)
        -- 2.10.2. inequalities
        have s2_10_2 : K ≥ 0 := by parley_order
        -- 2.10.3. inequalities
        have s2_10_3 : K ≤ N := by parley_order
        -- 2.10.4. def:range-between k := K, a := 0, b := N, from 2.10.2, 2.10.3
        have s2_10_4 : K ∈ Finset.Icc (0 : ℤ) N := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := K) (a := (0 : ℤ)) (b := N))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := K) (a := (0 : ℤ)) (b := N))).mpr (by parley_side); parley_side)
        -- 2.10.5. restate C2
        have s2_10_5 : ¬ K ∈ Finset.Icc (0 : ℤ) N := by parley_side
        all_goals parley_side
      -- 2.11. calculation
      have s2_11 : (LeanBridges.Counting.choose N K : ℤ) = (LeanBridges.Counting.choose N (N - K) : ℤ) := by
        calc (LeanBridges.Counting.choose N K : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := K) hC2)
          _ = (LeanBridges.Counting.choose N (N - K) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := N) (by parley_side) (k := N - K) s2_10); parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.BinomialBasics.ChooseComplement
