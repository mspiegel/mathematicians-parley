module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndexAgain

theorem names_the_index_again (T : ℤ → ℤ) (hD1 : T 0 = (0 : ℤ) ∧ (∀ j : ℤ, 0 ≤ j → T (j + 1) = T j + (j + 1))) :
    T 1 = 1 := by
  -- 1. thm:names-the-index
  exact (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) hD1)

end Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndexAgain
