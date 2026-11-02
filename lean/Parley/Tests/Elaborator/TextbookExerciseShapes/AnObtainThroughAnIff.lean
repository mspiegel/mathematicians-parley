module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIff

theorem an_obtain_through_an_iff (a : ℤ) (r : ℕ) (hH3 : (r : ℤ) < 3) (hH4 : a % (3 : ℤ) = (r : ℤ)) :
    (∃ q : ℤ, q * 3 + (r : ℤ) = a) := by
  -- 1. obtain q: mun:mod-remainder m := 3, from H3, H4
  obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := 3) (by parley_side) (r := r) (by parley_side))).mp (by parley_side)
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * 3 + (r : ℤ) = a := ⟨q, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIff
