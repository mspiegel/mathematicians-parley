module

public import AlgebraTactics
public import Functions
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence

/-! Written from proofs/hammack/fibonacci-even-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciEvenSum.FibonacciEvenSum

set_option maxHeartbeats 600000 in
theorem fibonacci_even_sum (n : ℤ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k)) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (F (2 * k) : ℤ)) = F (2 * n + 1) - 1 := by
  -- 1. thm:fibonacci-natural
  have s1 : ∀ k : ℤ, 0 ≤ k → 0 ≤ F k ∧ 0 ≤ G k := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side))
  -- 2. proof
  -- what this block shows, Lean's types give
  set q : ℤ → ℤ := fun k : ℤ => F (2 * k) with hD2
  -- 3. thm:fibonacci-recurrence
  have s3 : ∀ k : ℤ, 0 ≤ k → F (k + 2) = F k + F (k + 1) := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side))
  -- 4. induction on m starting at 1
  have s4 : ∀ m : ℤ, 0 < m → (∑ j ∈ Finset.Icc (1 : ℤ) m, (q j : ℤ)) = F (2 * m + 1) - 1 := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 4.1. proof
      -- what this block shows, Lean's types give
      -- 4.2. D1
      have s4_2 : F 1 = G 0 := by have h := (hD1.2.2 ((1 : ℤ) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 4.3. D1
      have s4_3 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
      -- 4.4. D1
      have s4_4 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
      -- 4.5. calculation
      have s4_5 : F 1 = 1 := by
        calc F 1 = G 0 := by exact s4_2
          _ = 1 := by exact s4_3
      -- 4.6. instantiate k := 0 in line 3
      have s4_6 : F 2 = F 0 + F 1 := by simpa only [zero_add] using (s3 (0 : ℤ) (by parley_side))
      -- 4.7. calculation
      have s4_7 : F (1 + 1) = 1 := by
        calc F (1 + 1) = F 2 := by norm_num
          _ = 1 := by linear_combination (norm := parley_norm) s4_4 + s4_5 + s4_6
      -- 4.8. instantiate k := 1 in line 3
      have s4_8 : F (1 + 2) = F 1 + F (1 + 1) := by exact (s3 (1 : ℤ) (by parley_side))
      -- 4.9. calculation
      have s4_9 : F (2 * 1 + 1) = 2 := by
        calc F (2 * 1 + 1) = F (1 + 2) := by norm_num
          _ = 2 := by linear_combination (norm := parley_norm) s4_5 + s4_7 + s4_8
      -- 4.10. calculation
      calc (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (q j : ℤ)) = q 1 := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ)))
        _ = F (2 * 1) := by simp (disch := omega) only [hD2]
        _ = F (1 + 1) := by norm_num
        _ = 1 := by exact s4_7
        _ = 2 - 1 := by norm_num
        _ = F (2 * 1 + 1) - 1 := by (have h := congrArg (fun t : ℤ => t - 1) s4_9.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
    | succ m hK3 hIH2 =>
      -- 4.11. proof
      -- what this block shows, Lean's types give
      -- 4.12. D2
      have s4_12 : q (m + 1) = F (2 * (m + 1)) := by simp (disch := omega) only [hD2]
      -- 4.13. instantiate k := 2m + 1 in line 3
      have s4_13 : F (2 * m + 1 + 2) = F (2 * m + 1) + F (2 * m + 1 + 1) := by exact (s3 (2 * m + 1) (by parley_side))
      -- 4.14. substitute
      have s4_14 : F (2 * (m + 1) + 1) = F (2 * m + 1) + F (2 * m + 1 + 1) := by
        have c1 : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by parley_ring
        have row1 : F (2 * (m + 1) + 1) = F (2 * m + 1) + F (2 * m + 1 + 1) := by (have h := Eq.subst (motive := (fun t : ℤ => F t = F (2 * m + 1) + F (2 * m + 1 + 1))) c1 s4_13; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.15. substitute
      have s4_15 : F (2 * (m + 1) + 1) = F (2 * m + 1) + F (2 * (m + 1)) := by
        have c1 : 2 * m + 1 + 1 = 2 * (m + 1) := by parley_ring
        have row1 : F (2 * (m + 1) + 1) = F (2 * m + 1) + F (2 * (m + 1)) := by (have h := Eq.subst (motive := (fun t : ℤ => F (2 * (m + 1) + 1) = F (2 * m + 1) + F t)) c1 s4_14; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.16. instantiate k := 2m + 1 in line 2
      -- 4.17. instantiate k := 2(m + 1) in line 2
      -- 4.18. calculation
      have r122_1 : m ≥ 1 := by parley_side
      calc (∑ j ∈ Finset.Icc (1 : ℤ) (m + 1), (q j : ℤ)) = (∑ j ∈ Finset.Icc (1 : ℤ) m, (q j : ℤ)) + q (m + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r122_1)
        _ = F (2 * m + 1) - 1 + q (m + 1) := by (have h := congrArg (fun t : ℤ => t + q (m + 1)) hIH2; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = F (2 * m + 1) - 1 + F (2 * (m + 1)) := by (have h := congrArg (fun t : ℤ => F (2 * m + 1) - 1 + t) s4_12; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = F (2 * (m + 1) + 1) - 1 := by linear_combination (norm := parley_norm) (-1) * s4_15
  -- 5. instantiate m := n in line 4, from D2
  exact (s4 n (by parley_side))

end Parley.Proofs.Hammack.FibonacciEvenSum.FibonacciEvenSum
