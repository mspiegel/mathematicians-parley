module

public import Functions
public import PowerTactics
public import Tactics
public import Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.DefinedInTheBody

theorem defined_in_the_body :
    (1 : ℤ) = 1 := by
  obtain ⟨T, hD1⟩ : ∃ T : ℤ → ℤ, T 0 = (0 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → T (k + 1) = T k + (k + 1) := LeanBridges.Functions.recursion_exists _ (fun k v => v + (k + 1))
  -- 1. thm:names-the-index
  have s1 : T 1 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); parley_side)
  -- 2. calculation
  have s2 : (1 : ℤ) = 1 := by
    calc (1 : ℤ) = T 1 := by parley_side
      _ = 1 := by parley_side
  all_goals exact s2

end Parley.Tests.Elaborator.RecursionShapesCited.DefinedInTheBody
