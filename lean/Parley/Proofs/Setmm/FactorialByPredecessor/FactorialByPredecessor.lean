module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/factorial-by-predecessor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor

theorem factorial_by_predecessor (N : ℤ) (hH1 : 0 < N) :
    (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N := by
  -- 1. mun:nat-minus-one n := N
  have s1 : 0 ≤ N - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) hH1)
  -- 2. def:nat0 n := N − 1, from 1
  have s2 : 0 < N - 1 ∨ N - 1 = 0 := by
    have hI : 0 < N - 1 ∨ N - 1 = 0 := by parley_instance (((Parley.Items.Stdlib.Numbers.def_nat0 (n := N - 1))).mp ⟨N - 1, s1, rfl⟩)
    exact hI
  -- 3. cases, from 2
  rcases s2 with hC1 | hC2
  · skip
    -- 3.1. algebra
    have s3_1 : N - 1 + 1 = N := by parley_ring
    -- 3.2. calculation
    calc (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (N - 1 + 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ)) s3_1.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.factorial (N - 1) : ℤ) * (N - 1 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N - 1) (le_of_lt hC1))
      _ = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial (N - 1) : ℤ) * t) s3_1; push_cast at h ⊢; all_goals exact_mod_cast h)
  · skip
    -- 3.3. algebra, from C2
    have s3_3 : N = 1 := by linear_combination (norm := parley_norm) hC2
    -- 3.4. calculation
    have s3_4 : (LeanBridges.Counting.factorial (N - 1) : ℤ) = 1 := by
      calc (LeanBridges.Counting.factorial (N - 1) : ℤ) = (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ)) hC2; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 := by norm_num
    -- 3.5. restate 3.3
    have s3_5 : 1 * N = 1 := by simpa only [one_mul] using s3_3
    -- 3.6. calculation
    calc (LeanBridges.Counting.factorial N : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ)) s3_3; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
      _ = 1 * N := s3_5.symm
      _ = (LeanBridges.Counting.factorial (N - 1) : ℤ) * N := by (have h := congrArg (fun t : ℤ => t * N) s3_4.symm; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor
