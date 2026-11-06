module

public import Tactics

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayInstantiated

theorem a_congruence_the_other_way_instantiated (a : ℤ) (n : ℤ) (hH2 : 0 < n) (hH3 : ∀ x : ℤ, (x ^ 2) ≡ x [ZMOD n]) :
    a ≡ (a ^ 2) [ZMOD n] := by
  -- 1. instantiate x := a in H3
  have s1 : a ≡ (a ^ 2) [ZMOD n] := by first | exact (hH3 a) | exact ((hH3 a)).symm | simpa using (hH3 a) | exact_mod_cast (hH3 a) | (have h := (hH3 a); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayInstantiated
