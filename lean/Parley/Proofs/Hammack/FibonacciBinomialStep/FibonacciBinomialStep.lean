module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/fibonacci-binomial-step.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep

set_option maxHeartbeats 1000000 in
theorem fibonacci_binomial_step (m : ℤ) (hH1 : 0 ≤ m) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1 + 1), ((LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) k : ℤ) : ℤ)) + (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (m - k) k : ℤ) : ℤ)) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. mun:sum-last n := m + 1, from 1
  have s3 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1 + 1), ((LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) : ℤ)) + (LeanBridges.Counting.choose (m + 1 + 1 - (m + 1 + 1)) (m + 1 + 1) : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ))) (n := m + 1) (by parley_side))
  -- 4. algebra
  have s4 : m + 1 + 1 - (m + 1 + 1) = 0 := by parley_ring
  -- 5. inequalities, from H1
  have s5 : 0 < m + 1 + 1 := by parley_order
  -- 6. calculation
  have s6 : (LeanBridges.Counting.choose (m + 1 + 1 - (m + 1 + 1)) (m + 1 + 1) : ℤ) = 0 := by
    calc (LeanBridges.Counting.choose (m + 1 + 1 - (m + 1 + 1)) (m + 1 + 1) : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) (m + 1 + 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (m + 1 + 1) : ℤ)) s4; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := m + 1 + 1)) s5
  -- 7. substitute C(((m + 1) + 1) − ((m + 1) + 1), (m + 1) + 1) = 0 (line 6) into line 3
  have s7 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1 + 1), ((LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) : ℤ)) := by first | parley_subst_at s6 s3 | (have e_nat : LeanBridges.Counting.choose (m + 1 + 1 - (m + 1 + 1)) (m + 1 + 1) = 0 := by exact_mod_cast s6; parley_subst_at e_nat s3)
  -- 8. proof
  have s8 : ∀ k : ℤ, k ∈ Finset.Icc 0 (m + 1) → (LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) = (LeanBridges.Counting.choose (m + 1 - k) k : ℤ) + (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 8.1. mun:range-difference a := 0, n := m + 1, from J
    have s8_1 : 0 ≤ m + 1 - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := m + 1) (k := k) hJ)
    -- 8.2. algebra
    have s8_2 : m + 1 - k + 1 = m + 1 + 1 - k := by parley_ring
    -- 8.3. calculation
    calc (LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) = (LeanBridges.Counting.choose (m + 1 - k + 1) k : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t k : ℤ)) (s8_2).symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.choose (m + 1 - k) k : ℤ) + (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1 - k) (by parley_side) (k := k)).symm
  -- 9. proof
  -- what this block shows, Lean's types give
  -- 10. proof
  -- what this block shows, Lean's types give
  -- 11. proof
  -- what this block shows, Lean's types give
  -- 12. mun:sum-first n := m + 1, from 10
  have s12 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) = (LeanBridges.Counting.choose (m + 1) (0 - 1 : ℤ) : ℤ) + (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) := by
    have hI : (∑ a ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - a) (a - 1) : ℤ) : ℤ)) = (LeanBridges.Counting.choose (m + 1 - 0) (0 - 1 : ℤ) : ℤ) + (∑ a ∈ Finset.Icc (0 + 1 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - a) (a - 1) : ℤ) : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ))) (n := m + 1) (by parley_side)))
    simpa only [sub_zero, zero_add] using hI
  -- 13. calculation
  have s13 : (LeanBridges.Counting.choose (m + 1) (0 - 1 : ℤ) : ℤ) = 0 := by
    calc (LeanBridges.Counting.choose (m + 1) (0 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (m + 1) (-1 : ℤ) : ℤ) := by norm_num
      _ = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_1 (n := m + 1) (by parley_side))
  -- 14. proof
  -- what this block shows, Lean's types give
  -- 15. substitute C(m + 1, 0 − 1) = 0 (line 13) into line 12
  have s15 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) := by first | parley_subst_at s13 s12 | (have e_nat : LeanBridges.Counting.choose (m + 1) (0 - 1 : ℤ) = 0 := by exact_mod_cast s13; parley_subst_at e_nat s12)
  -- 16. proof
  -- what this block shows, Lean's types give
  -- 17. proof
  have s17 : ∀ k : ℤ, k ∈ Finset.Icc 1 (m + 1) → (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) = (LeanBridges.Counting.choose (m - (k - 1)) (k - 1) : ℤ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 17.1. algebra
    have s17_1 : m + 1 - k = m - (k - 1) := by parley_ring
    -- 17.2. substitute (m + 1) − k = m − (k − 1) (line 17.1)
    (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (k - 1) : ℤ)) s17_1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 18. proof
  -- what this block shows, Lean's types give
  -- 19. calculation
  have s19 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (m - k) k : ℤ) : ℤ)) := by
    calc (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) := by exact s15
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m - (k - 1)) (k - 1) : ℤ) : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m - (k - 1)) (k - 1) : ℤ))) (a := (1 : ℤ)) (b := m + 1) s17)
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (m - k) k : ℤ) : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose (m - k) k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); parley_side)
  -- 20. calculation
  calc (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1 + 1), ((LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ) : ℤ)) := by exact s7
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) k : ℤ) + (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1 + 1 - k) k : ℤ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1 - k) k : ℤ) + (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ))) (a := (0 : ℤ)) (b := m + 1) s8)
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) k : ℤ) : ℤ)) + (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ) : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_add (t := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1 - k) k : ℤ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1 - k) (k - 1) : ℤ))) (a := (0 : ℤ)) (b := m + 1))
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) k : ℤ) : ℤ)) + (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (m - k) k : ℤ) : ℤ)) := by (have h := congrArg (fun t : ℤ => (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1 - k) k : ℤ) : ℤ)) + t) s19; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep
