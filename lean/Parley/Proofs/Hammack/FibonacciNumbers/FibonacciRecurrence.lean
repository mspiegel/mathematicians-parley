module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! Written from proofs/hammack/fibonacci-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence

theorem fibonacci_recurrence (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (∀ k : ℤ, 0 ≤ k → F (k + 2) = F k + F (k + 1)) := by
  -- 1. proof
  intro k hK1
  -- 1.1. D1
  have s1_1 : F (k + 1 + 1) = G (k + 1) := by have h := (hD1.2.2 ((k + 1 + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 1.2. D1
  have s1_2 : G (k + 1) = F k + G k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 1.3. D1
  have s1_3 : F (k + 1) = G k := by have h := (hD1.2.2 ((k + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 1.4. transitivity, from 1.1, 1.2
  have s1_4 : F (k + 1 + 1) = F k + G k := by parley_side
  -- 1.5. substitute F(k + 1) = G(k) (line 1.3) into line 1.4
  have s1_5 : F (k + 1 + 1) = F k + F (k + 1) := by parley_subst_at s1_3 s1_4
  -- 1.6. substitute
  have c1 : k + 1 + 1 = k + 2 := by parley_ring
  have row1 : F (k + 2) = F k + F (k + 1) := by parley_subst_at c1 s1_5
  exact row1

end Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence
