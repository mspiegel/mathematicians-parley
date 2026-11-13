module

public import Functions
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.DefinedInTheBody

theorem defined_in_the_body :
    (1 : ℤ) = 1 := by
  obtain ⟨T, hD1⟩ : ∃ T : ℤ → ℤ, T 0 = (0 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → T (k + 1) = T k + (k + 1)) := LeanBridges.Functions.recursion_exists _ (fun k v => v + (k + 1))
  -- 1. thm:names-the-index
  have s1 : T 1 = 1 := by exact (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) hD1)
  -- 2. calculation
  calc (1 : ℤ) = T 1 := by exact s1.symm
    _ = 1 := by exact s1

end Parley.Tests.Elaborator.RecursionShapesCited.DefinedInTheBody
