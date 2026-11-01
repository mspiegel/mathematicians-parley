module

public import Parley.Library

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayInstantiated

theorem a_congruence_the_other_way_instantiated (a : ℤ) (n : ℕ) (H2 : 0 < n) (H3 : ∀ x : ℤ, (x ^ 2) ≡ x [ZMOD (n : ℤ)]) :
    a ≡ (a ^ 2) [ZMOD (n : ℤ)] := by
  -- 1. instantiate x := a in H3
  have s1 : a ≡ (a ^ 2) [ZMOD (n : ℤ)] := by simpa using (H3 a)
  parley_side

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayInstantiated
