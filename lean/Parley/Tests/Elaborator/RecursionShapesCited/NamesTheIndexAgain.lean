module

public import PowerTactics
public import Tactics
public import Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndexAgain

theorem names_the_index_again (T : ℤ → ℤ) (hD1 : T 0 = (0 : ℤ) ∧ ∀ j : ℤ, 0 ≤ j → T (j + 1) = T j + (j + 1)) :
    T 1 = 1 := by
  -- 1. thm:names-the-index
  have s1 : T 1 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndex.names_the_index (T := T) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecursionShapesCited.NamesTheIndexAgain
