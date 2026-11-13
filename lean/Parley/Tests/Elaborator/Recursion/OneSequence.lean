module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! Written from tests/elaborator/recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Recursion.OneSequence

theorem one_sequence (c : ℤ → ℤ) (hD1 : c 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → c (k + 1) = 2 * c k)) :
    c (0 + 1) = 2 := by
  -- 1. D1
  have s1 : c 0 = 1 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
  -- 2. membership
  have s2 : (0 : ℤ) ≤ 0 := by norm_num
  -- 3. D1, from 2
  have s3 : c (0 + 1) = 2 * c 0 := by have h := (hD1.2 ((0 + 1 : ℤ) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 4. substitute c(0) = 1 (line 1)
  have s4 : 2 * c 0 = 2 * 1 := by (have h := congrArg (fun t : ℤ => 2 * t) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 5. arithmetic
  have s5 : (2 * 1 : ℤ) = 2 := by parley_arith
  -- 6. calculation
  calc c (0 + 1) = 2 * c 0 := s3
    _ = 2 * 1 := s4
    _ = 2 := by (have h := s5; revert h; norm_num)

end Parley.Tests.Elaborator.Recursion.OneSequence
