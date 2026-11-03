module

public import Tactics

/-! Written from proofs/hammack/fibonacci-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural

theorem fibonacci_natural (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (∀ k : ℕ, 0 ≤ F (k : ℤ) ∧ 0 ≤ G (k : ℤ)) := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, 0 ≤ F (k : ℤ) ∧ 0 ≤ G (k : ℤ) := by
    intro k
    induction k with
    | zero =>
      -- 1.1. D1
      have s1_1 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
      -- 1.2. D1
      have s1_2 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
      -- 1.3. membership, from 1.1
      have s1_3 : 0 ≤ F 0 := by parley_side
      -- 1.4. membership, from 1.2
      have s1_4 : 0 ≤ G 0 := by parley_side
      -- 1.5. join 1.3, 1.4
      have s1_5 : 0 ≤ F 0 ∧ 0 ≤ G 0 := by parley_side
      all_goals parley_side
    | succ k hIH =>
      -- 1.6. D1
      have s1_6 : F ((k : ℤ) + 1) = G (k : ℤ) := by have h := (hD1.2.2 (((k : ℤ) + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 1.7. D1
      have s1_7 : G ((k : ℤ) + 1) = F (k : ℤ) + G (k : ℤ) := by have h := (hD1.2.2 (((k : ℤ) + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 1.8. membership, from IH, 1.6
      have s1_8 : 0 ≤ F ((k : ℤ) + 1) := by parley_side
      -- 1.9. membership, from IH, 1.7
      have s1_9 : 0 ≤ G ((k : ℤ) + 1) := by parley_side
      -- 1.10. join 1.8, 1.9
      have s1_10 : 0 ≤ F ((k : ℤ) + 1) ∧ 0 ≤ G ((k : ℤ) + 1) := by parley_side
      all_goals parley_side
  all_goals exact s1

end Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
