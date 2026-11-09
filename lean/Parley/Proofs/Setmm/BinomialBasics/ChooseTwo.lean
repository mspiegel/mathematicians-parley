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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseTwo

set_option maxHeartbeats 600000 in
theorem choose_two (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose N (2 : ℤ) : ℚ) = (N : ℚ) * ((N : ℚ) - 1) / 2 := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ N = 0 := by simpa only [Int.cast_id, exists_eq_right] using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side)
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:nat-minus-one n := N, from C1
    have s2_1 : 0 ≤ N - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side))
    -- 2.2. def:nat0 n := N − 1, from 2.1
    have s2_2 : 0 < N - 1 ∨ N - 1 = 0 := by simpa only [Int.cast_id, exists_eq_right] using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := N - 1))).mp (by parley_side)
    -- 2.3. cases, from 2.2
    rcases s2_2 with hC3 | hC4
    · skip
      -- 2.3.1. mun:nat-minus-one n := N − 1, from C3
      have s2_3_1 : 0 ≤ N - 1 - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N - 1) (by parley_side))
      -- 2.3.2. inequalities, from C3
      have s2_3_2a : (0 : ℤ) ≤ 2 := by parley_order
      have s2_3_2b : 2 ≤ N := by parley_order
      -- 2.3.3. def:range-between k := 2, a := 0, b := N, from 2.3.2
      have s2_3_3 : (2 : ℤ) ∈ Finset.Icc (0 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range_between (k := (2 : ℤ)) (a := (0 : ℤ)) (b := N))).mpr (by parley_side)
      -- 2.3.4. algebra
      have s2_3_4 : N - 2 = N - 1 - 1 := by parley_ring
      -- 2.3.5. substitute N − 2 = (N − 1) − 1 (line 2.3.4)
      have s2_3_5 : (LeanBridges.Counting.factorial (N - 2) : ℤ) = (LeanBridges.Counting.factorial (N - 1 - 1) : ℤ) := by parley_subst s2_3_4
      -- 2.3.6. def:factorial n := 1
      have s2_3_6 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side))
      -- 2.3.7. substitute 1 + 1 = 2 (arithmetic) into line 2.3.6
      have s2_3_7 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * 2 := by parley_subst_at (show (1 + 1 : ℤ) = 2 by parley_side) s2_3_6
      -- 2.3.8. substitute
      have s2_3_8 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by
        have c1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
        have row1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_subst_at c1 s2_3_7
        exact row1
      -- 2.3.9. calculation
      have s2_3_9 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
        calc (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_side
          _ = 2 := by norm_num
      -- 2.3.10. thm:factorial-by-predecessor, from C1
      have s2_3_10 : (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N := by exact (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side))
      -- 2.3.11. substitute
      have s2_3_11 : (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (N - 1 - 1) : ℤ) * (N - 1) * N := by
        have c1 : (LeanBridges.Counting.factorial (N - 1) : ℤ) = (LeanBridges.Counting.factorial (N - 1 - 1) : ℤ) * (N - 1) := by exact (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N - 1) (by parley_side))
        have row1 : (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (N - 1 - 1) : ℤ) * (N - 1) * N := by parley_subst_at c1 s2_3_10
        exact row1
      -- 2.3.12. mun:factorial-nat n := (N − 1) − 1, from 2.3.1
      have s2_3_12 : 0 < (LeanBridges.Counting.factorial (N - 1 - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N - 1 - 1) (by parley_side))
      -- 2.3.13. calculation
      calc (LeanBridges.Counting.choose N (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - 2) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_3
        _ = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - 1 - 1) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by
            have s2_3_5_w : (LeanBridges.Counting.factorial (N - 2) : ℚ) = (LeanBridges.Counting.factorial (N - 1 - 1) : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_3_5; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s2_3_5_w | parley_subst s2_3_5
        _ = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - 1 - 1) : ℚ) * 2) := by
            have s2_3_9_w : (LeanBridges.Counting.factorial (2 : ℤ) : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_3_9; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s2_3_9_w | parley_subst s2_3_9
        _ = (LeanBridges.Counting.factorial (N - 1 - 1) : ℚ) * ((N : ℚ) - 1) * (N : ℚ) / ((LeanBridges.Counting.factorial (N - 1 - 1) : ℚ) * 2) := by
            have s2_3_11_w : (LeanBridges.Counting.factorial N : ℚ) = (LeanBridges.Counting.factorial (N - 1 - 1) : ℚ) * ((N : ℚ) - 1) * (N : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_3_11; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s2_3_11_w | parley_subst s2_3_11
        _ = (N : ℚ) * ((N : ℚ) - 1) / 2 := by parley_ring
    · skip
      -- 2.3.14. arithmetic
      have s2_3_14 : (1 : ℤ) < 2 := by parley_arith
      -- 2.3.15. substitute
      have s2_3_15 : N < 2 := by
        have c1 : 1 = N := by linear_combination (norm := parley_norm) (-1) * hC4
        have row1 : N < 2 := by parley_subst_at c1 s2_3_14
        exact row1
      -- 2.3.16. calculation
      calc (LeanBridges.Counting.choose N (2 : ℤ) : ℚ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15 | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15 | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15; parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_3_15; parley_side)
        _ = (N : ℚ) * ((N : ℚ) - 1) / 2 := by
            have hC4_w : (N : ℚ) - 1 = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hC4; push_cast at h; linear_combination (norm := parley_norm) h
            linear_combination (norm := parley_norm) ((-(N : ℚ)) / ((2))) * hC4_w
  · skip
    -- 2.4. arithmetic
    have s2_4 : (0 : ℤ) < 2 := by parley_arith
    -- 2.5. substitute N = 0 (C2) into line 2.4
    have s2_5 : N < 2 := by parley_subst_at hC2 s2_4
    -- 2.6. calculation
    calc (LeanBridges.Counting.choose N (2 : ℤ) : ℚ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5 | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5 | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5; parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (2 : ℤ))) s2_5; parley_side)
      _ = (N : ℚ) * ((N : ℚ) - 1) / 2 := by
          have hC2_w : (N : ℚ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hC2; push_cast at h; linear_combination (norm := parley_norm) h
          linear_combination (norm := parley_norm) ((-(N : ℚ) + 1) / ((2))) * hC2_w

end Parley.Proofs.Setmm.BinomialBasics.ChooseTwo
