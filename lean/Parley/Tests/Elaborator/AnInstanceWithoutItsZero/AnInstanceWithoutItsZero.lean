module

public import LeanBridges

/-! Written from tests/elaborator/an-instance-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInstanceWithoutItsZero.AnInstanceWithoutItsZero

theorem an_instance_without_its_zero (a : ℤ → ℝ) (hH2 : ∀ k : ℕ, a ((k : ℤ) + 1) = a (k : ℤ) + 2) :
    a 1 = a 0 + 2 := by
  -- 1. instantiate k := 0 in H2
  have s1 : a 1 = a 0 + 2 := by first | linear_combination (norm := parley_norm) (hH2 0) | (have h := (hH2 0); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (hH2 0) | exact_mod_cast ((hH2 0)).symm | (have h := (hH2 0); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 0); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Elaborator.AnInstanceWithoutItsZero.AnInstanceWithoutItsZero
