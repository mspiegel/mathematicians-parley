module

public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-recursion-header-and-an-assumption.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARecursionHeaderAndAnAssumption.ARecursionHeaderAndAnAssumption

theorem a_recursion_header_and_an_assumption (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1)) (hH1 : F 1 = 2) :
    F 1 + 1 = 3 := by
  -- 1. substitute F(1) = 2 (H1)
  have s1 : F 1 + 1 = 2 + 1 := by parley_subst hH1
  -- 2. calculation
  calc F 1 + 1 = 2 + 1 := by parley_side
    _ = 3 := by norm_num

end Parley.Tests.Elaborator.ARecursionHeaderAndAnAssumption.ARecursionHeaderAndAnAssumption
