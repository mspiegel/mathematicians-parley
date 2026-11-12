module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor

/-! Written from proofs/setmm/choose-two-less.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoLess.ChooseTwoLess

theorem choose_two_less (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose (N + 1) (N - 1) : ℚ) = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ N = 0 := by
    have hI : 0 < N ∨ N = 0 := by parley_instance (((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side))
    exact hI
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:nat-minus-one n := N, from C1
    have s2_1 : 0 ≤ N - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) hC1)
    -- 2.2. def:nat0 n := N − 1, from 2.1
    have s2_2 : 0 < N - 1 ∨ N - 1 = 0 := by
      have hI : 0 < N - 1 ∨ N - 1 = 0 := by parley_instance (((Parley.Items.Stdlib.Numbers.def_nat0 (n := N - 1))).mp (by parley_side))
      exact hI
    -- 2.3. cases, from 2.2
    rcases s2_2 with hC3 | hC4
    · skip
      -- 2.3.1. mun:factorial-nat n := N − 1, from C3
      have s2_3_1 : 0 < (LeanBridges.Counting.factorial (N - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N - 1) (le_of_lt hC3))
      -- 2.3.2. inequalities, from C1
      have s2_3_2a : 0 ≤ N - 1 := by linarith only [hC1]
      have s2_3_2b : N - 1 ≤ N + 1 := by linarith only []
      -- 2.3.3. def:range-between k := N − 1, a := 0, b := N + 1, from 2.3.2
      have s2_3_3 : N - 1 ∈ Finset.Icc (0 : ℤ) (N + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := N - 1) (a := (0 : ℤ)) (b := N + 1))).mpr ⟨s2_3_2a, s2_3_2b⟩
      -- 2.3.4. algebra
      have s2_3_4 : N + 1 - (N - 1) = 2 := by parley_ring
      -- 2.3.5. def:factorial n := 1
      have s2_3_5 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side))
      -- 2.3.6. substitute 1 + 1 = 2 (arithmetic) into line 2.3.5
      have s2_3_6 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * 2 := by
        have e_arith : (1 + 1 : ℤ) = 2 := by parley_arith
        (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * t)) e_arith s2_3_5; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 2.3.7. substitute
      have s2_3_7 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by
        have c1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
        have row1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = t * 2)) c1 s2_3_6; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 2.3.8. calculation
      have s2_3_8 : (LeanBridges.Counting.factorial (N + 1 - (N - 1)) : ℤ) = 2 := by
        calc (LeanBridges.Counting.factorial (N + 1 - (N - 1)) : ℤ) = (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ)) s2_3_4; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 1 * 2 := by exact s2_3_7
          _ = 2 := by norm_num
      -- 2.3.9. thm:factorial-by-predecessor, from C1
      have s2_3_9 : (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N := by exact (Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor.factorial_by_predecessor (N := N) hC1)
      -- 2.3.10. calculation
      have s2_3_10 : (LeanBridges.Counting.factorial (N + 1) : ℤ) = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N * (N + 1) := by
        calc (LeanBridges.Counting.factorial (N + 1) : ℤ) = (LeanBridges.Counting.factorial N : ℤ) * (N + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) hH1)
          _ = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N * (N + 1) := by (have h := congrArg (fun t : ℤ => t * (N + 1)) s2_3_9; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 2.3.11. calculation
      calc (LeanBridges.Counting.choose (N + 1) (N - 1) : ℚ) = (LeanBridges.Counting.factorial (N + 1) : ℚ) / ((LeanBridges.Counting.factorial (N + 1 - (N - 1)) : ℚ) * (LeanBridges.Counting.factorial (N - 1) : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N - 1)) s2_3_3
        _ = (LeanBridges.Counting.factorial (N + 1) : ℚ) / (2 * (LeanBridges.Counting.factorial (N - 1) : ℚ)) := by
            have e_w : (LeanBridges.Counting.factorial (N + 1 - (N - 1)) : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_3_8; push_cast at h; linear_combination (norm := parley_norm) h
            (have h := congrArg (fun t : ℚ => (LeanBridges.Counting.factorial (N + 1) : ℚ) / (t * (LeanBridges.Counting.factorial (N - 1) : ℚ))) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (LeanBridges.Counting.factorial (N - 1) : ℚ) * (N : ℚ) * ((N : ℚ) + 1) / (2 * (LeanBridges.Counting.factorial (N - 1) : ℚ)) := by
            have e_w : (LeanBridges.Counting.factorial (N + 1) : ℚ) = (LeanBridges.Counting.factorial (N - 1) : ℚ) * (N : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_3_10; push_cast at h; linear_combination (norm := parley_norm) h
            (have h := congrArg (fun t : ℚ => t / (2 * (LeanBridges.Counting.factorial (N - 1) : ℚ))) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = ((N : ℚ) + 1) * (N : ℚ) / 2 := by parley_ring
    · skip
      -- 2.3.12. calculation
      calc (LeanBridges.Counting.choose (N + 1) (N - 1) : ℚ) = (LeanBridges.Counting.choose (N + 1) (0 : ℤ) : ℚ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose (N + 1) t : ℤ)) hC4; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 := by
            have hI : (LeanBridges.Counting.choose (N + 1) (0 : ℤ) : ℚ) = 1 := by parley_instance_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := N + 1) (by parley_side)))
            exact hI
        _ = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
            have hC4_w : (N : ℚ) - 1 = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hC4; push_cast at h; linear_combination (norm := parley_norm) h
            linear_combination (norm := parley_norm) ((-(N : ℚ) - 2) / ((2))) * hC4_w
  · skip
    -- 2.4. algebra, from C2
    have s2_4 : N + 1 = 1 := by linear_combination (norm := parley_norm) hC2
    -- 2.5. algebra, from C2
    have s2_5 : N - 1 = -1 := by linear_combination (norm := parley_norm) hC2
    -- 2.6. calculation
    calc (LeanBridges.Counting.choose (N + 1) (N - 1) : ℚ) = (LeanBridges.Counting.choose (1 : ℤ) (N - 1) : ℚ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (N - 1) : ℤ)) s2_4; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.choose (1 : ℤ) (-1 : ℤ) : ℚ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose (1 : ℤ) t : ℤ)) s2_5; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 0 := by exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_1 (n := (1 : ℤ)) (by parley_side))
      _ = ((N : ℚ) + 1) * (N : ℚ) / 2 := by
          have hC2_w : (N : ℚ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hC2; push_cast at h; linear_combination (norm := parley_norm) h
          linear_combination (norm := parley_norm) ((-(N : ℚ) - 1) / ((2))) * hC2_w

end Parley.Proofs.Setmm.ChooseTwoLess.ChooseTwoLess
