module

public import AlgebraTactics
public import Functions
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
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
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence

/-! Written from proofs/hammack/fibonacci-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciSum.FibonacciSum

theorem fibonacci_sum (n : ℤ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k)) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (F k : ℤ)) = F (n + 2) - 1 := by
  -- 1. thm:fibonacci-natural
  have s1 : ∀ k : ℤ, 0 ≤ k → 0 ≤ F k ∧ 0 ≤ G k := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) hD1)
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. thm:fibonacci-recurrence
  have s3 : ∀ k : ℤ, 0 ≤ k → F (k + 2) = F k + F (k + 1) := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) hD1)
  -- 4. induction on m starting at 1
  have s4 : ∀ m : ℤ, 0 < m → (∑ j ∈ Finset.Icc (1 : ℤ) m, (F j : ℤ)) = F (m + 2) - 1 := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 4.1. proof
      -- what this block shows, Lean's types give
      -- 4.2. mun:sum-single a := 1
      have s4_2 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (F j : ℤ)) = F 1 := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := F) (a := (1 : ℤ)))
      -- 4.3. D1
      have s4_3 : F 1 = G 0 := by have h := (hD1.2.2 ((1 : ℤ) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 4.4. D1
      have s4_4 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
      -- 4.5. D1
      have s4_5 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
      -- 4.6. calculation
      have s4_6 : F 1 = 1 := by
        calc F 1 = G 0 := s4_3
          _ = 1 := s4_4
      -- 4.7. instantiate k := 0 in line 3
      have s4_7 : F 2 = F 0 + F 1 := by simpa only [zero_add, Int.cast_zero] using (s3 (0 : ℤ) (by norm_num))
      -- 4.8. calculation
      have s4_8 : F (1 + 1) = 1 := by
        calc F (1 + 1) = F 2 := by norm_num
          _ = 1 := by linear_combination (norm := parley_norm) s4_5 + s4_6 + s4_7
      -- 4.9. instantiate k := 1 in line 3
      have s4_9 : F (1 + 2) = F 1 + F (1 + 1) := by exact (s3 (1 : ℤ) (by norm_num))
      -- 4.10. algebra, from 4.6, 4.8, 4.9
      have s4_10 : F (1 + 2) = 2 := by linear_combination (norm := parley_norm) s4_6 + s4_8 + s4_9
      -- 4.11. algebra, from 4.2, 4.6, 4.10
      linear_combination (norm := parley_norm) s4_2 + s4_6 + (-1) * s4_10
    | succ m hK3 hIH2 =>
      -- 4.12. proof
      -- what this block shows, Lean's types give
      -- 4.13. mun:sum-extended a := 1, n := m
      have r87_1 : m ≥ 1 := by exact lt_of_lt_of_le zero_lt_one hK3
      have s4_13 : (∑ j ∈ Finset.Icc (1 : ℤ) (m + 1), (F j : ℤ)) = (∑ j ∈ Finset.Icc (1 : ℤ) m, (F j : ℤ)) + F (m + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := F) (a := (1 : ℤ)) (n := m) r87_1)
      -- 4.14. instantiate k := m + 1 in line 3
      have s4_14 : F (m + 1 + 2) = F (m + 1) + F (m + 1 + 1) := by exact (s3 (m + 1) (add_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hK3)) (by norm_num)))
      -- 4.15. substitute
      have s4_15 : F (m + 1 + 2) = F (m + 1) + F (m + 2) := by
        have c1 : m + 1 + 1 = m + 2 := by parley_ring
        have row1 : F (m + 1 + 2) = F (m + 1) + F (m + 2) := by (have h := Eq.subst (motive := (fun t : ℤ => F (m + 1 + 2) = F (m + 1) + F t)) c1 s4_14; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.16. instantiate k := m + 2 in line 2
      -- 4.17. instantiate k := m + 1 in line 2
      -- 4.18. algebra, from IH2, 4.13, 4.15
      linear_combination (norm := parley_norm) hIH2 + s4_13 + (-1) * s4_15
  -- 5. instantiate m := n in line 4
  exact (s4 n hH1)

end Parley.Proofs.Hammack.FibonacciSum.FibonacciSum
