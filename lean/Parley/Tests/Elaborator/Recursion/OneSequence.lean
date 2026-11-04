module

public import ArithTactics
public import SubstTactics
public import Tactics

/-! Written from tests/elaborator/recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Recursion.OneSequence

theorem one_sequence (c : ℤ → ℤ) (hD1 : c 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → c (k + 1) = 2 * c k) :
    c (0 + 1) = 2 := by
  -- 1. D1
  have s1 : c 0 = 1 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
  -- 2. membership
  have s2 : (0 : ℤ) ≤ 0 := by parley_side
  -- 3. D1, from 2
  have s3 : c (0 + 1) = 2 * c 0 := by have h := (hD1.2 ((0 + 1 : ℤ) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 4. substitute c(0) = 1 (line 1)
  have s4 : 2 * c 0 = 2 * 1 := by parley_subst s1
  -- 5. arithmetic
  have s5 : (2 * 1 : ℤ) = 2 := by parley_arith
  -- 6. calculation
  have s6 : c (0 + 1) = 2 := by
    calc c (0 + 1) = 2 * c 0 := by parley_side
      _ = 2 * 1 := by parley_side
      _ = 2 := by parley_side
  all_goals exact s6

end Parley.Tests.Elaborator.Recursion.OneSequence
