module

public import SetTactics
public import SubstTactics
public import Tactics

/-! Written from tests/elaborator/a-part-substituted-into.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APartSubstitutedInto.APartSubstitutedInto

theorem a_part_substituted_into {α : Type*} (X : Set α) (R : Set α) (hH2 : R ⊆ X) (hH3 : X = ∅) :
    R ⊆ ∅ := by
  -- 1. substitute X = ∅ (H3) into H2
  have s1 : R ⊆ ∅ := by parley_subst_at hH3 hH2
  all_goals exact s1

end Parley.Tests.Elaborator.APartSubstitutedInto.APartSubstitutedInto
