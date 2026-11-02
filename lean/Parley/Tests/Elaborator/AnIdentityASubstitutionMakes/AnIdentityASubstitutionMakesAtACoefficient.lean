module

public import LeanBridges

/-! Written from tests/elaborator/an-identity-a-substitution-makes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtACoefficient

theorem an_identity_a_substitution_makes_at_a_coefficient (N : ℕ) (k : ℤ) (hH3 : (1 ^ k : ℚ) = 1) :
    (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ k = (LeanBridges.Counting.choose (N : ℤ) k : ℚ) := by
  -- 1. substitute 1^k = 1 (H3)
  have s1 : (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ k = (LeanBridges.Counting.choose (N : ℤ) k : ℚ) := by parley_subst hH3
  all_goals parley_side

end Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtACoefficient
