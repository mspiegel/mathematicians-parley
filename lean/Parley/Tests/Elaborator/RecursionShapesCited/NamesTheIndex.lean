module

public import SubstTactics
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

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex

theorem names_the_index (T : ℤ → ℤ) (hD1 : T 0 = (0 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → T (k + 1) = T k + (k + 1))) :
    T 1 = 1 := by
  -- 1. D1
  have s1 : T 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
  -- 2. D1
  have s2 : T (0 + 1) = T 0 + (0 + 1) := by have h := (hD1.2 ((0 + 1 : ℤ) - 1) (by omega)); simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 3. substitute T(0) = 0 (line 1)
  have s3 : T 0 + (0 + 1) = 0 + (0 + 1) := by parley_subst s1
  -- 4. calculation
  calc T 1 = T (0 + 1) := by norm_num
    _ = T 0 + (0 + 1) := by exact s2
    _ = 0 + (0 + 1) := by exact s3
    _ = 1 := by norm_num

end Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex
