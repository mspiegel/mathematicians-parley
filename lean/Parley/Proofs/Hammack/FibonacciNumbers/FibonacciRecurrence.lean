module

public import Tactics

/-! Written from proofs/hammack/fibonacci-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence

theorem fibonacci_recurrence (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (∀ k : ℕ, F ((k : ℤ) + 2) = F (k : ℤ) + F ((k : ℤ) + 1)) := by
  -- 1. proof
  have s1 : ∀ k : ℕ, F ((k : ℤ) + 2) = F (k : ℤ) + F ((k : ℤ) + 1) := by
    intro k
    -- 1.1. D1
    have s1_1 : F ((k : ℤ) + 1 + 1) = G ((k : ℤ) + 1) := by have h := (hD1.2.2 (((k : ℤ) + 1 + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
    -- 1.2. D1
    have s1_2 : G ((k : ℤ) + 1) = F (k : ℤ) + G (k : ℤ) := by have h := (hD1.2.2 (((k : ℤ) + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
    -- 1.3. D1
    have s1_3 : F ((k : ℤ) + 1) = G (k : ℤ) := by have h := (hD1.2.2 (((k : ℤ) + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
    -- 1.4. transitivity, from 1.1, 1.2
    have s1_4 : F ((k : ℤ) + 1 + 1) = F (k : ℤ) + G (k : ℤ) := by parley_side
    -- 1.5. substitute F(k + 1) = G(k) (line 1.3) into line 1.4
    have s1_5 : F ((k : ℤ) + 1 + 1) = F (k : ℤ) + F ((k : ℤ) + 1) := by parley_subst_at s1_3 s1_4
    -- 1.6. substitute
    have s1_6 : F ((k : ℤ) + 2) = F (k : ℤ) + F ((k : ℤ) + 1) := by
      have c1 : (k : ℤ) + 1 + 1 = (k : ℤ) + 2 := by parley_ring
      have row1 : F ((k : ℤ) + 2) = F (k : ℤ) + F ((k : ℤ) + 1) := by parley_subst_at c1 s1_5
      exact row1
    all_goals exact s1_6
  all_goals exact s1

end Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence
