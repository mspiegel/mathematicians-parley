module

public import Functions
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! Written from proofs/hammack/fibonacci-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural

theorem fibonacci_natural (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k)) :
    (∀ k : ℤ, 0 ≤ k → 0 ≤ F k ∧ 0 ≤ G k) := by
  -- 1. induction on k starting at 0
  intro k h_k
  replace h_k : 0 ≤ k := by omega
  induction k, h_k using LeanBridges.Functions.le_induction with
  | base =>
    -- 1.1. D1
    have s1_1 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
    -- 1.2. D1
    have s1_2 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
    -- 1.3. membership, from 1.1
    have s1_3 : 0 ≤ F 0 := le_of_le_of_eq (by norm_num) (s1_1).symm
    -- 1.4. membership, from 1.2
    have s1_4 : 0 ≤ G 0 := le_of_le_of_eq (by norm_num) (s1_2).symm
    -- 1.5. join 1.3, 1.4
    have s1_5 : 0 ≤ F 0 ∧ 0 ≤ G 0 := ⟨s1_3, s1_4⟩
    exact ⟨(s1_5).1, (s1_5).2⟩
  | succ k hK hIH =>
    -- 1.6. D1
    have s1_6 : F (k + 1) = G k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
    -- 1.7. D1
    have s1_7 : G (k + 1) = F k + G k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
    -- 1.8. membership, from IH, 1.6
    have s1_8 : 0 ≤ F (k + 1) := le_of_le_of_eq (hIH.2) (s1_6).symm
    -- 1.9. membership, from IH, 1.7
    have s1_9 : 0 ≤ G (k + 1) := le_of_le_of_eq (add_nonneg (hIH.1) (hIH.2)) (s1_7).symm
    -- 1.10. join 1.8, 1.9
    have s1_10 : 0 ≤ F (k + 1) ∧ 0 ≤ G (k + 1) := ⟨s1_8, s1_9⟩
    exact ⟨(s1_10).1, (s1_10).2⟩

end Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
