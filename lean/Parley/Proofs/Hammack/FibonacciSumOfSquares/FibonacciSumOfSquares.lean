module

public import AlgebraTactics
public import Functions
public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence

/-! Written from proofs/hammack/fibonacci-sum-of-squares.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciSumOfSquares.FibonacciSumOfSquares

set_option maxHeartbeats 600000 in
theorem fibonacci_sum_of_squares (n : ℤ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (F k ^ 2 : ℤ)) = F n * F (n + 1) := by
  -- 1. thm:fibonacci-natural
  have s1 : ∀ k : ℤ, 0 ≤ k → 0 ≤ F k ∧ 0 ≤ G k := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side))
  -- 2. proof
  -- what this block shows, Lean's types give
  set q : ℤ → ℤ := fun j => F j ^ 2 with hD2
  -- 3. thm:fibonacci-recurrence
  have s3 : ∀ k : ℤ, 0 ≤ k → F (k + 2) = F k + F (k + 1) := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side))
  -- 4. induction on m starting at 1
  have s4 : ∀ m : ℤ, 0 < m → (∑ j ∈ Finset.Icc (1 : ℤ) m, (q j : ℤ)) = F m * F (m + 1) := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 4.1. proof
      -- what this block shows, Lean's types give
      -- 4.2. mun:sum-single a := 1
      have s4_2 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (q j : ℤ)) = q 1 := by exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ)))
      -- 4.3. D1
      have s4_3 : F 1 = G 0 := by have h := (hD1.2.2 ((1 : ℤ) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 4.4. D1
      have s4_4 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
      -- 4.5. D1
      have s4_5 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
      -- 4.6. calculation
      have s4_6 : F 1 = 1 := by
        calc F 1 = G 0 := by parley_side
          _ = 1 := by parley_side
      -- 4.7. instantiate k := 0 in line 3
      have s4_7 : F 2 = F 0 + F 1 := by simpa only [zero_add] using (s3 (0 : ℤ) (by parley_side))
      -- 4.8. calculation
      have s4_8 : F (1 + 1) = 1 := by
        calc F (1 + 1) = F 2 := by norm_num
          _ = 1 := by linear_combination (norm := parley_norm) s4_5 + s4_6 + s4_7
      -- 4.9. algebra, from D2, 4.2, 4.6, 4.8
      try simp only [hD2] at *
      try push_cast at *
      linear_combination (norm := parley_norm) s4_2 + (-F (1 + 1) + F 1 + 1) * s4_6 + (-1) * s4_8
    | succ m hK3 hIH2 =>
      -- 4.10. proof
      -- what this block shows, Lean's types give
      -- 4.11. mun:sum-extended a := 1, n := m
      have r90_1 : m ≥ 1 := by parley_side
      have s4_11 : (∑ j ∈ Finset.Icc (1 : ℤ) (m + 1), (q j : ℤ)) = (∑ j ∈ Finset.Icc (1 : ℤ) m, (q j : ℤ)) + q (m + 1) := by exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r90_1)
      -- 4.12. instantiate k := m in line 3
      have s4_12 : F (m + 2) = F m + F (m + 1) := by exact (s3 m (by parley_side))
      -- 4.13. instantiate k := m in line 2
      -- 4.14. instantiate k := m + 1 in line 2
      -- 4.15. algebra, from D2, IH2, 4.11, 4.12
      have s4_15 : (∑ j ∈ Finset.Icc (1 : ℤ) (m + 1), (q j : ℤ)) = F (m + 1) * F (m + 2) := by
        try simp only [hD2] at *
        try push_cast at *
        linear_combination (norm := parley_norm) hIH2 + s4_11 + (-F (m + 1)) * s4_12
      -- 4.16. substitute
      have c1 : m + 2 = m + 1 + 1 := by parley_ring
      have row1 : (∑ j ∈ Finset.Icc (1 : ℤ) (m + 1), (q j : ℤ)) = F (m + 1) * F (m + 1 + 1) := by parley_subst_at c1 s4_15
      exact row1
  -- 5. instantiate m := n in line 4, from D2
  linear_combination (norm := parley_norm) (s4 n (by parley_side))

end Parley.Proofs.Hammack.FibonacciSumOfSquares.FibonacciSumOfSquares
