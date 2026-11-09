module

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

/-! Written from tests/elaborator/citing-a-theorem-over-a-header-recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne

theorem counted_to_one (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1)) :
    F 1 = 1 := by
  -- 1. D1
  have s1 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
  -- 2. D1
  have s2 : F (0 + 1) = F 0 + 1 := by have h := (hD1.2 ((0 + 1 : ℤ) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 3. substitute F(0) = 0 (line 1)
  have s3 : F 0 + 1 = 0 + 1 := by (have h := congrArg (fun t : ℤ => t + 1) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. calculation
  calc F 1 = F (0 + 1) := by norm_num
    _ = F 0 + 1 := by exact s2
    _ = 0 + 1 := by exact s3
    _ = 1 := by norm_num

end Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne
