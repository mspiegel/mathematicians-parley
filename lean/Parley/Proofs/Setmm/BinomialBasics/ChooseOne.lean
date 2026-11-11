module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
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
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseOne

set_option maxHeartbeats 400000 in
theorem choose_one (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose N (1 : ℤ) : ℤ) = N := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ N = 0 := by
    have hI : 0 < N ∨ N = 0 := by parley_instance (((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side))
    exact hI
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:nat-minus-one n := N, from C1
    have s2_1 : 0 ≤ N - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side))
    -- 2.2. inequalities, from C1
    have s2_2a : (0 : ℤ) ≤ 1 := by parley_order
    have s2_2b : 1 ≤ N := by parley_order
    -- 2.3. def:range-between k := 1, a := 0, b := N, from 2.2
    have s2_3 : (1 : ℤ) ∈ Finset.Icc (0 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range_between (k := (1 : ℤ)) (a := (0 : ℤ)) (b := N))).mpr (by parley_side)
    -- 2.4. def:factorial
    have s2_4 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
    -- 2.5. thm:factorial-by-predecessor, from C1
    have s2_5 : (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N := by exact (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) (by parley_side))
    -- 2.6. mun:factorial-nat n := N − 1, from 2.1
    have s2_6 : 0 < (LeanBridges.Counting.factorial (N - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N - 1) (by parley_side))
    -- 2.7. calculation
    try qify
    calc (LeanBridges.Counting.choose N (1 : ℤ) : ℚ) = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - 1) : ℚ) * (LeanBridges.Counting.factorial (1 : ℤ) : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := (1 : ℤ))) s2_3
      _ = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - 1) : ℚ) * 1) := by
          have e_w : (LeanBridges.Counting.factorial (1 : ℤ) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun t : ℚ => (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - 1) : ℚ) * t)) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.factorial (N - 1) : ℚ) * (N : ℚ) / ((LeanBridges.Counting.factorial (N - 1) : ℚ) * 1) := by
          have e_w : (LeanBridges.Counting.factorial N : ℚ) = (LeanBridges.Counting.factorial (N - 1) : ℚ) * (N : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun t : ℚ => t / ((LeanBridges.Counting.factorial (N - 1) : ℚ) * 1)) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (N : ℚ) := by parley_ring
  · skip
    -- 2.8. arithmetic
    have s2_8 : (0 : ℤ) < 1 := by parley_arith
    -- 2.9. substitute N = 0 (C2) into line 2.8
    have s2_9 : N < 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t < 1)) (hC2).symm s2_8; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.10. calculation
    calc (LeanBridges.Counting.choose N (1 : ℤ) : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := N) (by parley_side) (k := (1 : ℤ))) s2_9
      _ = N := by parley_side

end Parley.Proofs.Setmm.BinomialBasics.ChooseOne
