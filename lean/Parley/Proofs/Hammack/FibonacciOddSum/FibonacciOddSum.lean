module

public import AlgebraTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
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
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence

/-! Written from proofs/hammack/fibonacci-odd-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciOddSum.FibonacciOddSum

set_option maxHeartbeats 600000 in
theorem fibonacci_odd_sum (n : ℤ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (F (2 * k - 1) : ℤ)) = F (2 * n) := by
  -- 1. thm:fibonacci-natural
  have s1 : ∀ k : ℤ, 0 ≤ k → 0 ≤ F k ∧ 0 ≤ G k := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side))
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. proof
  have s3 : ∀ k : ℤ, 0 < k → 0 < 2 * k - 1 := by
    intro k hK2
    -- 3.1. inequalities, from K2
    have s3_1 : 0 < 2 * k - 1 := by parley_order
    -- 3.2. mun:pos-int-nat m := 2k − 1, from 3.1
    exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := 2 * k - 1) s3_1)
  set q : ℤ → ℤ := fun k => F (2 * k - 1) with hD2
  -- 4. thm:fibonacci-recurrence
  have s4 : ∀ k : ℤ, 0 ≤ k → F (k + 2) = F k + F (k + 1) := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side))
  -- 5. induction on m starting at 1
  have s5 : ∀ m : ℤ, 0 < m → (∑ j ∈ Finset.Icc (1 : ℤ) m, (q j : ℤ)) = F (2 * m) := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 5.1. proof
      -- what this block shows, Lean's types give
      -- 5.2. D1
      have s5_2 : F 1 = G 0 := by have h := (hD1.2.2 ((1 : ℤ) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 5.3. D1
      have s5_3 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
      -- 5.4. D1
      have s5_4 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
      -- 5.5. calculation
      have s5_5 : F 1 = 1 := by
        calc F 1 = G 0 := by parley_side
          _ = 1 := by parley_side
      -- 5.6. instantiate k := 0 in line 4
      have s5_6 : F 2 = F 0 + F 1 := by simpa only [zero_add] using (s4 (0 : ℤ) (by parley_side))
      -- 5.7. calculation
      have s5_7 : F (1 + 1) = 1 := by
        calc F (1 + 1) = F 2 := by norm_num
          _ = 1 := by linear_combination (norm := parley_norm) s5_4 + s5_5 + s5_6
      -- 5.8. calculation
      calc (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (q j : ℤ)) = q 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); parley_side)
        _ = F (2 * 1 - 1) := by simp (disch := omega) only [hD2]
        _ = F 1 := by norm_num
        _ = 1 := by parley_side
        _ = F (1 + 1) := by parley_side
        _ = F (2 * 1) := by norm_num
    | succ m hK4 hIH2 =>
      -- 5.9. proof
      -- what this block shows, Lean's types give
      -- 5.10. D2
      have s5_10 : q (m + 1) = F (2 * (m + 1) - 1) := by simp (disch := omega) only [hD2]
      -- 5.11. substitute
      have s5_11 : q (m + 1) = F (2 * m + 1) := by
        have c1 : 2 * (m + 1) - 1 = 2 * m + 1 := by parley_ring
        have row1 : q (m + 1) = F (2 * m + 1) := by parley_subst_at c1 s5_10
        exact row1
      -- 5.12. instantiate k := 2m in line 4
      have s5_12 : F (2 * m + 2) = F (2 * m) + F (2 * m + 1) := by exact (s4 (2 * m) (by parley_side))
      -- 5.13. substitute
      have s5_13 : F (2 * (m + 1)) = F (2 * m) + F (2 * m + 1) := by
        have c1 : 2 * m + 2 = 2 * (m + 1) := by parley_ring
        have row1 : F (2 * (m + 1)) = F (2 * m) + F (2 * m + 1) := by parley_subst_at c1 s5_12
        exact row1
      -- 5.14. calculation
      have r125_1 : m ≥ 1 := by parley_side
      calc (∑ j ∈ Finset.Icc (1 : ℤ) (m + 1), (q j : ℤ)) = (∑ j ∈ Finset.Icc (1 : ℤ) m, (q j : ℤ)) + q (m + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := m) r125_1); parley_side)
        _ = F (2 * m) + q (m + 1) := by parley_subst hIH2
        _ = F (2 * m) + F (2 * m + 1) := by parley_subst s5_11
        _ = F (2 * (m + 1)) := by parley_side
  -- 6. instantiate m := n in line 5, from D2
  linear_combination (norm := parley_norm) (s5 n (by parley_side))

end Parley.Proofs.Hammack.FibonacciOddSum.FibonacciOddSum
